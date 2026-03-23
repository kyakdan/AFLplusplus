# Value Profiling

Value profiling (VP) adds a distance signal on top of normal edge coverage.
Instead of only asking whether a comparison was reached, AFL++ also tracks how
close the observed operands are to a match. This helps on transformed compares
where direct solve attempts are weak or impossible.

## Activation

Value profiling currently uses runtime VP instrumentation in the main target.
Compile the target with `AFL_LLVM_VALUEPROFILE=1` or
`AFL_LLVM_VALUE_PROFILE=1`.

- `-r0`: enable value profiling from startup
- `-rN`: enable value profiling after `N` seconds without new edge coverage,
  and disable it again after edge coverage recovers

Without `-r`, value profiling stays disabled.

`AFL_VALUE_PROFILE_SLOTS=K` controls the number of tracked runtime slots. The
valid range is `1..16`.

## Frontier

VP maintains a frontier of the best known distances for `(site, slot)` pairs.
Queue entries owning frontier slots are favored for more fuzzing. Runtime VP
keeps multiple runtime replicas per slot so independent operand streams at the
same comparison site do not overwrite each other immediately.

## VP Taint

Runtime VP can run a per-entry taint analysis that answers a narrower question:
which input byte positions affect the owned VP sites for this queue entry?

The current implementation is observational:

- it only runs for entries that currently own VP frontier sites
- it replays the input against the runtime VP map without polluting the real
  persistent VP state
- it stores the result per owned site, not as one global input-wide bitmap

The analysis is two-phase:

1. coarse perturbation marks byte regions that can change owned-site VP state
2. per-byte replay confirms the final sensitive positions

Only runtime VP uses this taint analysis.

## Freshness And Rebuilds

Each queue entry tracks:

- the current sorted set of owned VP sites
- the generation of that owned-site set
- the generation that the stored taint result matches

Stored taint is current when both generations match. When the owned-site set
changes, AFL++ marks the taint stale and rebuilds it after repeated stale
visits. Partial in-memory resume state is discarded immediately when the
owned-site generation changes.

An entry may also have a valid analyzed result with no sensitive bytes. That
is different from missing coverage and is persisted explicitly.

## Persistence

Completed VP taint is stored in:

`queue/.state/vp_taint/<queue-id>`

The persisted state stores:

- input length
- VP slot count
- the sorted analyzed-site set
- the sorted non-empty per-site taint entries

On load, AFL++ rejects corrupted or incompatible state, including:

- wrong input length
- wrong VP slot count
- unsorted or duplicate site ids
- per-site entries that are not members of the analyzed-site set

If the loaded analyzed-site set still covers the entry's current owned sites,
the taint result is treated as current. Otherwise AFL++ keeps it as stale
fallback data and rebuilds it later.
