/* GCC plugin for PC Guard edge coverage instrumentation for AFL++.

   Copyright 2014-2019 Free Software Foundation, Inc
   Copyright 2015, 2016 Google Inc. All rights reserved.
   Copyright 2019-2024 AdaCore

   Originally written by Alexandre Oliva <oliva@adacore.com>, based on the AFL
   LLVM pass by Laszlo Szekeres <lszekeres@google.com> and Michal
   Zalewski <lcamtuf@google.com>.

   Rewritten to use PC Guard mechanism (like LLVM's SanitizerCoveragePCGUARD)
   for collision-free edge coverage with true edge instrumentation via
   critical edge splitting.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.

 */

/* This GCC plugin implements PC Guard edge coverage instrumentation.

   The approach mirrors LLVM's SanitizerCoveragePCGUARD:

   1. Split all critical edges to enable true edge coverage
   2. Use dominator-based pruning to skip redundant blocks
   3. Create per-function guard arrays in __sancov_guards section
   4. Emit a per-TU constructor that passes linker-provided guard bounds
      to __sanitizer_cov_trace_pc_guard_init
   5. At runtime, the init function assigns globally unique IDs to guards
   6. Each instrumented block loads its guard value and uses it as map index

   The AFL++ runtime (afl-compiler-rt.o.c) receives guard ranges from those
   constructors and performs the ID assignment in a platform-independent way.

   Benefits over the previous XOR-based approach:
   - Collision-free: unique IDs assigned at runtime across all modules
   - True edge coverage: critical edge splitting instruments actual edges
   - Compatible with existing AFL++ runtime infrastructure
*/

#include "afl-gcc-common.h"

#if defined(__has_include) && __has_include("memmodel.h")
  #include "memmodel.h"
#endif

/* This plugin, being under the same license as GCC, satisfies the
   "GPL-compatible Software" definition in the GCC RUNTIME LIBRARY
   EXCEPTION, so it can be part of an "Eligible" "Compilation
   Process".  */
int plugin_is_GPL_compatible = 1;

namespace {

/* Identify compiler-generated static ctor/dtor wrappers robustly across
   GCC versions. Older plugin headers may miss DECL_STATIC_* macros, so
   we fall back to GCC-generated wrapper naming conventions. */
static inline bool is_artificial_static_ctor_dtor(const_tree decl) {

  if (!decl) return false;

#ifdef DECL_STATIC_CONSTRUCTOR
  if (DECL_STATIC_CONSTRUCTOR(decl)) return true;
#endif
#ifdef DECL_STATIC_DESTRUCTOR
  if (DECL_STATIC_DESTRUCTOR(decl)) return true;
#endif

  const_tree ident = DECL_NAME(decl);
  const char *name = ident ? IDENTIFIER_POINTER(ident) : NULL;

  const char *asm_name = NULL;
  tree        asm_ident = DECL_ASSEMBLER_NAME(const_cast<tree>(decl));
  if (asm_ident) asm_name = IDENTIFIER_POINTER(asm_ident);

  /* Common GCC-generated init/fini wrapper names:
     - prefixes "_sub_I_" / "_sub_D_" (cgraph_build_static_cdtor wrappers)
     - prefixes "_GLOBAL__sub_I_" / "_GLOBAL__sub_D_" (C++ wrappers)
     - "__static_initialization_and_destruction_" helpers (unmangled)
     - "_Z41__static_initialization_and_destruction_" (Itanium mangled)

     Some GCC versions do not mark all wrappers as DECL_ARTIFICIAL, so keep
     this fallback independent of DECL_ARTIFICIAL and also check the assembler
     symbol name. */
  auto matches_wrapper_name = [](const char *n) {

    if (!n) return false;

    return !strncmp(n, "_sub_I_", 7) || !strncmp(n, "_sub_D_", 7) ||
           !strncmp(n, "_GLOBAL__sub_I_", 15) ||
           !strncmp(n, "_GLOBAL__sub_D_", 15) ||
           !strncmp(n, "__static_initialization_and_destruction_", 41) ||
           !strncmp(n, "_Z41__static_initialization_and_destruction_", 45);

  };

  return matches_wrapper_name(name) || matches_wrapper_name(asm_name);

}

/* Section name for guard arrays - depends on target object format.
   The plugin emits a per-TU constructor (emit_pcguard_ctor) that calls
   __sanitizer_cov_trace_pc_guard_init with linker-generated section
   bounds, so the runtime assigns unique IDs to every guard at startup.

   ELF (Linux, BSD): section "__sancov_guards"
     -> linker creates __start___sancov_guards / __stop___sancov_guards

   Mach-O (macOS): section "__DATA,__sancov_guards"
     -> linker creates section$start$__DATA$__sancov_guards /
                       section$end$__DATA$__sancov_guards

   We use OBJECT_FORMAT_MACHO (defined by GCC based on target) rather than
   __APPLE__ (host platform) to correctly handle cross-compilation.
*/
static const char *getSanCovSectionName() {
#if defined(OBJECT_FORMAT_MACHO)
  return "__DATA,__sancov_guards";
#else
  return "__sancov_guards";
#endif
}

/* Unique counter for guard array names to avoid conflicts.  */
static unsigned int sancov_id_counter = 0;

/* Track whether this TU created any guard arrays (used for ctor emission).  */
static bool sancov_guards_emitted = false;
static bool sancov_ctor_emitted = false;

static constexpr struct pass_data afl_pass_data = {

    .type = GIMPLE_PASS,
    .name = "afl",
    .optinfo_flags = OPTGROUP_NONE,
    .tv_id = TV_NONE,
    .properties_required = 0,
    .properties_provided = 0,
    .properties_destroyed = 0,
    .todo_flags_start = 0,
    .todo_flags_finish = (TODO_update_ssa | TODO_cleanup_cfg),

};

struct afl_pass : afl_base_pass {

  afl_pass(bool quiet)
      : afl_base_pass(quiet, !!getenv("AFL_DEBUG"), afl_pass_data),
        neverZero(!getenv("AFL_GCC_SKIP_NEVERZERO")), inst_blocks(0) {

    /* Note: initInstrumentList() is called by afl_base_pass constructor */

  }

  /* Should we make sure the map edge-crossing counters never wrap
     around to zero?  */
  const bool neverZero;

  /* Count instrumented blocks (edges after splitting).  */
  unsigned int inst_blocks;

  /* Per-function guard array (set during execute()).  */
  tree function_guard_array;

  /* Create and return a declaration for __afl_area_ptr.  */
  static inline tree get_afl_area_ptr_decl() {

    tree type = build_pointer_type(unsigned_char_type_node);
    tree decl = build_decl(BUILTINS_LOCATION, VAR_DECL,
                           get_identifier("__afl_area_ptr"), type);
    TREE_PUBLIC(decl) = 1;
    DECL_EXTERNAL(decl) = 1;
    DECL_ARTIFICIAL(decl) = 1;
    TREE_STATIC(decl) = 1;

    return decl;

  }

  /* Create a per-function guard array placed in sancov_guards section.
     For COMDAT functions we intentionally keep per-TU guard arrays (no weak
     cross-TU coalescing), because different TUs may produce different guard
     counts for the same function body under different optimization settings.  */
  tree create_function_guard_array(unsigned int num_guards) {

    if (num_guards == 0) return NULL_TREE;

    /* Create array type: uint32_t[num_guards]  */
    tree array_type = build_array_type_nelts(uint32_type_node, num_guards);

    /* Create variable declaration with unique name.
       Use static counter for uniqueness (like LLVM's __sancov_gen_).  */
    char name[64];
    snprintf(name, sizeof(name), "__sancov_gen_.%u", sancov_id_counter++);

    tree decl =
        build_decl(BUILTINS_LOCATION, VAR_DECL, get_identifier(name), array_type);

    /* Set attributes  */
    TREE_PUBLIC(decl) = 0;       /* Not exported  */
    TREE_STATIC(decl) = 1;       /* Static storage  */
    DECL_ARTIFICIAL(decl) = 1;   /* Compiler-generated  */
    TREE_USED(decl) = 1;         /* Mark as used  */
    DECL_PRESERVE_P(decl) = 1;   /* Prevent elimination  */
    TREE_ADDRESSABLE(decl) = 1;  /* We take its address  */

    /* Zero-initialize  */
    DECL_INITIAL(decl) = build_constructor(array_type, NULL);

    /* Place in sancov_guards section  */
    set_decl_section_name(decl, getSanCovSectionName());

    /* Emit the variable  */
    varpool_node::finalize_decl(decl);

    sancov_guards_emitted = true;

    return decl;

  }

  /* Emit a TU-level ctor that calls __sanitizer_cov_trace_pc_guard_init
     with the sancov_guards section bounds. Instrumented objects still
     require AFL runtime symbols at load/link time.  */
  static void emit_pcguard_ctor(void) {

    if (!sancov_guards_emitted || sancov_ctor_emitted) { return; }
    sancov_ctor_emitted = true;

    /* Build (weak) decl for __sanitizer_cov_trace_pc_guard_init */
    tree guard_ptr_type = build_pointer_type(uint32_type_node);
    tree fn_type =
        build_function_type_list(void_type_node, guard_ptr_type, guard_ptr_type,
                                 NULL_TREE);
    tree init_decl = build_fn_decl("__sanitizer_cov_trace_pc_guard_init",
                                   fn_type);
    TREE_PUBLIC(init_decl) = 1;
    DECL_EXTERNAL(init_decl) = 1;
    DECL_WEAK(init_decl) = 1;
    DECL_ARTIFICIAL(init_decl) = 1;

    /* Build decls for section start/stop symbols */
#if defined(OBJECT_FORMAT_MACHO)
    tree start_decl = build_decl(
        BUILTINS_LOCATION, VAR_DECL, get_identifier("sancov_guards_start"),
        uint32_type_node);
    tree stop_decl = build_decl(
        BUILTINS_LOCATION, VAR_DECL, get_identifier("sancov_guards_stop"),
        uint32_type_node);
    TREE_PUBLIC(start_decl) = 1;
    TREE_PUBLIC(stop_decl) = 1;
    DECL_EXTERNAL(start_decl) = 1;
    DECL_EXTERNAL(stop_decl) = 1;
    DECL_WEAK(start_decl) = 1;
    DECL_WEAK(stop_decl) = 1;
    DECL_ARTIFICIAL(start_decl) = 1;
    DECL_ARTIFICIAL(stop_decl) = 1;
    overwrite_decl_assembler_name(
        start_decl, get_identifier("*section$start$__DATA$__sancov_guards"));
    overwrite_decl_assembler_name(
        stop_decl, get_identifier("*section$end$__DATA$__sancov_guards"));
#else
    tree start_decl = build_decl(
        BUILTINS_LOCATION, VAR_DECL, get_identifier("__start___sancov_guards"),
        uint32_type_node);
    tree stop_decl = build_decl(
        BUILTINS_LOCATION, VAR_DECL, get_identifier("__stop___sancov_guards"),
        uint32_type_node);
    TREE_PUBLIC(start_decl) = 1;
    TREE_PUBLIC(stop_decl) = 1;
    DECL_EXTERNAL(start_decl) = 1;
    DECL_EXTERNAL(stop_decl) = 1;
    DECL_WEAK(start_decl) = 1;
    DECL_WEAK(stop_decl) = 1;
    DECL_ARTIFICIAL(start_decl) = 1;
    DECL_ARTIFICIAL(stop_decl) = 1;
#endif

    tree start_addr = build1(ADDR_EXPR, guard_ptr_type, start_decl);
    tree stop_addr = build1(ADDR_EXPR, guard_ptr_type, stop_decl);

    /* if (&start != NULL && &stop != NULL && &start != &stop && init) */
    tree nonnull_start =
        build2(NE_EXPR, boolean_type_node, start_addr,
               fold_convert(guard_ptr_type, null_pointer_node));
    tree nonnull_stop =
        build2(NE_EXPR, boolean_type_node, stop_addr,
               fold_convert(guard_ptr_type, null_pointer_node));
    tree different =
        build2(NE_EXPR, boolean_type_node, start_addr, stop_addr);
    tree init_ptr =
        build1(ADDR_EXPR, ptr_type_node, init_decl);
    tree init_nonnull =
        build2(NE_EXPR, boolean_type_node, init_ptr,
               fold_convert(ptr_type_node, null_pointer_node));

    tree cond = build2(TRUTH_ANDIF_EXPR, boolean_type_node, nonnull_start,
                       nonnull_stop);
    cond = build2(TRUTH_ANDIF_EXPR, boolean_type_node, cond, different);
    cond = build2(TRUTH_ANDIF_EXPR, boolean_type_node, cond, init_nonnull);

    tree call = build_call_expr(init_decl, 2, start_addr, stop_addr);
    tree if_stmt = build3(COND_EXPR, void_type_node, cond, call,
                          build_empty_stmt(BUILTINS_LOCATION));

    tree body = alloc_stmt_list();
    append_to_statement_list(if_stmt, &body);

    cgraph_build_static_cdtor('I', body, 2);

  }

  /* Check if BB contains a returns_twice call (e.g., setjmp).  */
  inline bool block_has_returns_twice(basic_block bb) {

    for (gimple_stmt_iterator gsi = gsi_start_bb(bb); !gsi_end_p(gsi);
         gsi_next(&gsi)) {

      if (gimple_code(gsi_stmt(gsi)) == GIMPLE_CALL) {

        if (gimple_call_flags(gsi_stmt(gsi)) & ECF_RETURNS_TWICE) return true;

      }

    }

    return false;

  }

  /* Check if BB is a "full dominator" - dominates ALL its successors.
     Based on LLVM's isFullDominator.  */
  bool is_full_dominator(basic_block bb) {

    if (EDGE_COUNT(bb->succs) == 0) return false;

    edge          e;
    edge_iterator ei;
    FOR_EACH_EDGE(e, ei, bb->succs) {

      if (!dominated_by_p(CDI_DOMINATORS, e->dest, bb)) return false;

    }

    return true;

  }

  /* Check if BB is a "full post-dominator" - post-dominates ALL predecessors.
     Based on LLVM's isFullPostDominator.  */
  bool is_full_post_dominator(basic_block bb) {

    if (EDGE_COUNT(bb->preds) == 0) return false;

    edge          e;
    edge_iterator ei;
    FOR_EACH_EDGE(e, ei, bb->preds) {

      if (!dominated_by_p(CDI_POST_DOMINATORS, e->src, bb)) return false;

    }

    return true;

  }

  /* Split critical edges while ignoring unreachable fallthrough destinations,
     matching LLVM's IgnoreUnreachableDests behavior.

     On GCC < 8, assert_unreachable_fallthru_edge_p is not declared in
     tree-cfg.h, so fall back to split_edges_for_insertion() which splits
     all critical edges unconditionally (a few extra blocks, but they are
     filtered out by should_instrument_block's __builtin_unreachable check).  */
#if GCC_VERSION >= 8000
  void split_pcguard_edges(function *fn) {

    auto_vec<edge> edges_to_split;
    basic_block    bb;
    edge           e;
    edge_iterator  ei;

    FOR_EACH_BB_FN(bb, fn) {

      FOR_EACH_EDGE(e, ei, bb->succs) {

        if (!EDGE_CRITICAL_P(e)) continue;
        if (e->flags & EDGE_COMPLEX) continue;
        if ((e->flags & EDGE_FALLTHRU) &&
            assert_unreachable_fallthru_edge_p(e))
          continue;
        edges_to_split.safe_push(e);

      }

    }

    for (unsigned i = 0; i < edges_to_split.length(); i++) {

      split_edge(edges_to_split[i]);

    }

  }

#else
  void split_pcguard_edges(function *) {

    split_edges_for_insertion();

  }

#endif

  /* Main block selection logic - matches LLVM's shouldInstrumentBlock
     with additional handling for returns_twice blocks.  */
  bool should_instrument_block(basic_block bb, function *fn) {

    /* Skip entry and exit pseudo-blocks  */
    if (bb == ENTRY_BLOCK_PTR_FOR_FN(fn)) return false;
    if (bb == EXIT_BLOCK_PTR_FOR_FN(fn)) return false;

    /* Skip blocks without a valid insertion point or unreachable blocks.  */
    gimple_stmt_iterator gsi = gsi_after_labels(bb);
    if (gsi_end_p(gsi)) {

      /* split_edge() creates empty blocks for critical edges; instrument them
         unless they are truly unreachable.  */
      if (EDGE_COUNT(bb->preds) == 0) return false;
      return true;

    }
    if (gimple_code(gsi_stmt(gsi)) == GIMPLE_CALL &&
        gimple_call_builtin_p(gsi_stmt(gsi), BUILT_IN_UNREACHABLE))
      return false;

    /* Entry block (first real block) - always instrument if reachable.  */
    if (bb == single_succ_edge(ENTRY_BLOCK_PTR_FOR_FN(fn))->dest) return true;

/* GCC versions < 15 can ICE in purge_dead_edges during RTL CFG cleanup when
   side-effecting instrumentation is injected into EH-only dispatcher/resx
   blocks produced by coroutine lowering. Restrict this workaround to
   coroutine-related functions. */
#if GCC_VERSION < 15000
    if (fn->coroutine_component) {

      for (gimple_stmt_iterator gsi = gsi_start_bb(bb); !gsi_end_p(gsi);
           gsi_next(&gsi)) {

        gimple           stmt = gsi_stmt(gsi);
        enum gimple_code code = gimple_code(stmt);
        if (code == GIMPLE_EH_DISPATCH || code == GIMPLE_RESX) return false;

      }

    }

#endif

    /* Returns_twice blocks (setjmp): skip if only reachable via longjmp  */
    if (block_has_returns_twice(bb)) {

      bool          has_normal_pred = false;
      edge          e;
      edge_iterator ei;
      FOR_EACH_EDGE(e, ei, bb->preds) {

        if (!(e->flags & EDGE_ABNORMAL)) {

          has_normal_pred = true;
          break;

        }

      }

      if (!has_normal_pred) return false;

    }

    /* Skip full dominators - their execution is implied by successors  */
    if (is_full_dominator(bb)) return false;

    /* Skip full post-dominators with multiple predecessors  */
    if (is_full_post_dominator(bb) && !single_pred_p(bb)) return false;

    return true;

  }

  /* Insert guard-based instrumentation into a basic block.
     Matches LLVM's approach exactly:
       1. Load guard value (map index)
       2. Load map pointer (in every block - let optimizer hoist)
       3. GEP to map entry
       4. Load counter, add 1, (NeverZero: if zero add 1), store  */
  void insert_guard_instrumentation(basic_block bb, unsigned int guard_idx) {

    gimple_seq seq = NULL;
    static tree afl_area_ptr_decl = get_afl_area_ptr_decl();

    /* Load guard value: edge_id = guard_array[guard_idx]  */
    tree guard_ref =
        build4(ARRAY_REF, uint32_type_node, function_guard_array,
               build_int_cst(sizetype, guard_idx), NULL_TREE, NULL_TREE);
    tree edge_id = create_tmp_var(uint32_type_node, ".edge_id");
    gimple_seq_add_stmt(&seq, gimple_build_assign(edge_id, guard_ref));

    /* Load map pointer (like LLVM - in every block)  */
    tree map_ptr = create_tmp_var(TREE_TYPE(afl_area_ptr_decl), ".afl_map_ptr");
    gimple_seq_add_stmt(&seq, gimple_build_assign(map_ptr, afl_area_ptr_decl));

    /* Compute map entry address: entry = map_ptr + edge_id  */
    tree edge_id_sized = create_tmp_var(sizetype, ".edge_id_sized");
    gimple_seq_add_stmt(
        &seq, gimple_build_assign(edge_id_sized, NOP_EXPR, edge_id));

    tree entry = create_tmp_var(TREE_TYPE(map_ptr), ".afl_map_entry");
    gimple_seq_add_stmt(
        &seq, gimple_build_assign(entry, POINTER_PLUS_EXPR, map_ptr, edge_id_sized));

    /* Load counter, increment, store  */
    tree memref = build2(MEM_REF, unsigned_char_type_node, entry,
                         build_zero_cst(TREE_TYPE(entry)));
    tree counter = create_tmp_var(unsigned_char_type_node, ".afl_counter");
    gimple_seq_add_stmt(&seq, gimple_build_assign(counter, memref));

    /* counter = counter + 1  */
    tree one = build_one_cst(unsigned_char_type_node);
    gimple_seq_add_stmt(&seq, gimple_build_assign(counter, PLUS_EXPR, counter, one));

    if (neverZero) {

      /* NeverZero: if counter wrapped to 0, set it to 1
         Same logic as LLVM: carry = (counter == 0); counter += carry  */
      tree zero = build_zero_cst(unsigned_char_type_node);
      tree is_zero = create_tmp_var(boolean_type_node, ".is_zero");
      gimple_seq_add_stmt(&seq, gimple_build_assign(is_zero, EQ_EXPR, counter, zero));

      tree carry = create_tmp_var(unsigned_char_type_node, ".carry");
      gimple_seq_add_stmt(&seq, gimple_build_assign(carry, NOP_EXPR, is_zero));

      gimple_seq_add_stmt(&seq, gimple_build_assign(counter, PLUS_EXPR, counter, carry));

    }

    /* Store counter back  */
    gimple_seq_add_stmt(&seq, gimple_build_assign(unshare_expr(memref), counter));

    /* Insert at block start (after labels)  */
    gimple_stmt_iterator insp = gsi_after_labels(bb);
    gsi_insert_seq_before(&insp, seq, GSI_SAME_STMT);

  }

  virtual unsigned int execute(function *fn) {

    /* Do not instrument compiler-generated static ctor/dtor wrappers
       (e.g. the TU-level PC Guard init ctor emitted below). Keep
       user-defined constructors instrumentable. */
    if (is_artificial_static_ctor_dtor(fn->decl)) return 0;

    if (!isInInstrumentList(fn)) return 0;

    /* Respect __attribute__((no_sanitize_coverage)) (GCC 14+).
       On older GCC the attribute is unrecognized/dropped, so
       lookup_attribute returns NULL_TREE (safe no-op).  */
    if (lookup_attribute("no_sanitize_coverage", DECL_ATTRIBUTES(fn->decl)))
      return 0;

    /* 1. Split critical edges for true edge coverage.  */
    split_pcguard_edges(fn);

    /* 2. Free any stale dominance info (CFG was modified)  */
    if (dom_info_available_p(CDI_DOMINATORS))
      free_dominance_info(CDI_DOMINATORS);
    if (dom_info_available_p(CDI_POST_DOMINATORS))
      free_dominance_info(CDI_POST_DOMINATORS);

    /* 3. Compute fresh dominance info  */
    calculate_dominance_info(CDI_DOMINATORS);
    calculate_dominance_info(CDI_POST_DOMINATORS);

    /* 4. Collect blocks to instrument (no CFG changes here)  */
    auto_vec<basic_block>  blocks_to_instrument;
    hash_set<basic_block>  returns_twice_blocks;
    basic_block            bb;

    FOR_EACH_BB_FN(bb, fn) {

      if (!should_instrument_block(bb, fn)) continue;

      blocks_to_instrument.safe_push(bb);

      if (block_has_returns_twice(bb)) { returns_twice_blocks.add(bb); }

    }

    /* 5. Early exit if nothing to instrument  */
    unsigned int num_guards = blocks_to_instrument.length();
    if (num_guards == 0) {

      /* split_pcguard_edges() above may have invalidated dominance data.
         Even when we do not instrument this function, leaving stale
         dominance info behind can trip later GCC todo passes. */
      if (dom_info_available_p(CDI_DOMINATORS))
        free_dominance_info(CDI_DOMINATORS);
      if (dom_info_available_p(CDI_POST_DOMINATORS))
        free_dominance_info(CDI_POST_DOMINATORS);
      return 0;

    }

    /* 6. Create guard array for this function  */
    function_guard_array = create_function_guard_array(num_guards);

    /* 7. Instrument collected blocks  */
    unsigned int guard_idx = 0;
    for (unsigned i = 0; i < blocks_to_instrument.length(); i++) {

      bb = blocks_to_instrument[i];

      /* Handle returns_twice blocks (setjmp) - create trampoline  */
      if (returns_twice_blocks.contains(bb)) {

        /* Free dominance info before CFG modification  */
        if (dom_info_available_p(CDI_DOMINATORS))
          free_dominance_info(CDI_DOMINATORS);
        if (dom_info_available_p(CDI_POST_DOMINATORS))
          free_dominance_info(CDI_POST_DOMINATORS);

        /* Split block to create trampoline  */
        edge        split_e = split_block_after_labels(bb);
        basic_block trampoline = bb;
        basic_block original = split_e->dest;

        /* Redirect abnormal edges to bypass trampoline  */
        auto_vec<edge> abnormal_preds;
        edge           e;
        edge_iterator  ei;
        FOR_EACH_EDGE(e, ei, trampoline->preds) {

          if (e->flags & EDGE_ABNORMAL) abnormal_preds.safe_push(e);

        }

        for (unsigned j = 0; j < abnormal_preds.length(); j++) {

          redirect_edge_succ(abnormal_preds[j], original);

        }

        /* Insert instrumentation in trampoline  */
        insert_guard_instrumentation(trampoline, guard_idx++);

      } else {

        /* Normal case: insert instrumentation at block start  */
        insert_guard_instrumentation(bb, guard_idx++);

      }

    }

    inst_blocks += guard_idx;

    /* Free dominance info since we may have modified CFG  */
    if (dom_info_available_p(CDI_DOMINATORS))
      free_dominance_info(CDI_DOMINATORS);
    if (dom_info_available_p(CDI_POST_DOMINATORS))
      free_dominance_info(CDI_POST_DOMINATORS);

    /* Rebuild callgraph edges: the inline instrumentation references
       __afl_area_ptr and the guard arrays, introducing new variable
       references that the callgraph must track.  */
    return TODO_rebuild_cgraph_edges;

  }

  /* Plugin finalize callback - print summary.  */
  static void plugin_finalize(void *, void *p) {

    opt_pass *op = (opt_pass *)p;
    afl_pass &self = (afl_pass &)*op;

    if (!self.be_quiet) {

      if (!self.inst_blocks)
        WARNF("No instrumentation targets found.");
      else
        OKF("Instrumented %u edges (PC Guard mode, %s).", self.inst_blocks,
            getenv("AFL_HARDEN") ? G_("hardened") : G_("non-hardened"));

    }

  }

};

static void pcguard_start_unit(void *, void *) {

  sancov_guards_emitted = false;
  sancov_ctor_emitted = false;

}

static void pcguard_finish_unit(void *, void *) {

  afl_pass::emit_pcguard_ctor();

}

static struct plugin_info afl_plugin = {

    .version = "20250205",
    .help = G_("AFL++ GCC plugin (PC Guard edge coverage)\n\
\n\
Platform: ELF (Linux, BSD) and Mach-O (macOS)\n\
Architecture: Any (x86, x86_64, ARM, AArch64, RISC-V, etc.)\n\
\n\
Environment variables:\n\
  AFL_QUIET              - Suppress output\n\
  AFL_GCC_ONLY_FSRV      - Disable instrumentation (forkserver only)\n\
  AFL_GCC_SKIP_NEVERZERO - Disable NeverZero counter handling\n\
  AFL_INST_RATIO         - Handled at runtime by AFL++ runtime\n\
\n\
Removed (no longer supported):\n\
  AFL_GCC_OUT_OF_LINE    - Was: out-of-line call-based instrumentation.\n\
                           Now always uses inline PC Guard instrumentation.\n\
"),

};

}  // namespace

/* Plugin initialization - register callbacks.  */
int plugin_init(struct plugin_name_args   *info,
                struct plugin_gcc_version *version) {

  if (!plugin_default_version_check(version, &gcc_version) &&
      !getenv("AFL_GCC_DISABLE_VERSION_CHECK"))
    FATAL(G_("GCC and plugin have incompatible versions, expected GCC %s, "
             "is %s"),
          gcc_version.basever, version->basever);

  /* Show a banner.  */
  bool quiet = false;
  if (isatty(2) && !getenv("AFL_QUIET")) {

    SAYF(cCYA "afl-gcc-pass " cBRI VERSION cRST
              " by <oliva@adacore.com, aflplusplus@gmail.com>\n");

  } else {

    quiet = true;

  }

  /* Warn about removed/changed environment variables.  */
  if (getenv("AFL_GCC_OUT_OF_LINE"))
    WARNF(
        "AFL_GCC_OUT_OF_LINE is no longer supported. The GCC plugin now uses "
        "PC Guard instrumentation which is always inline. Ignoring.");

  bool fsrv_only =
      !!(getenv("AFL_GCC_ONLY_FSRV") || getenv("AFL_GCC_ONLY_FRSV"));

  const char *name = info->base_name;
  if (!fsrv_only) { register_callback(name, PLUGIN_INFO, NULL, &afl_plugin); }

  afl_pass                 *aflp = new afl_pass(quiet);
  struct register_pass_info pass_info = {

      .pass = aflp,
      .reference_pass_name = "ssa",
      .ref_pass_instance_number = 1,
      .pos_op = PASS_POS_INSERT_AFTER,

  };

  if (!fsrv_only) {

    register_callback(name, PLUGIN_PASS_MANAGER_SETUP, NULL, &pass_info);
    register_callback(name, PLUGIN_FINISH, afl_pass::plugin_finalize,
                      pass_info.pass);
    register_callback(name, PLUGIN_START_UNIT, pcguard_start_unit, nullptr);
    register_callback(name, PLUGIN_FINISH_UNIT, pcguard_finish_unit, nullptr);

  }

  if (fsrv_only) {

    ACTF("Instrumentation disabled due to AFL_GCC_ONLY_FSRV");

  } else if (!quiet) {

    ACTF(G_("PC Guard edge coverage instrumentation (%s mode)."),
         getenv("AFL_HARDEN") ? G_("hardened") : G_("non-hardened"));

  }

  return 0;

}
