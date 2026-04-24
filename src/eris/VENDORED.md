# Vendored eris framework (from clutch)

This directory (`src/eris/`) is a vendored copy of the probabilistic-logic
framework from the [clutch] repo. We pull it in so that lambda-veris can wire
its own λRust-based language into clutch's eris-style probabilistic weakest
precondition (with error credits) without taking a hard opam dependency on the
clutch package.

The Coq namespace is renamed from `clutch` (upstream) to `eris` here — we
only use the eris-style fragment of clutch, so the shorter name is apt.
During vendoring, every `From clutch.xxx Require ...` in the copied files
was rewritten to `From eris.xxx Require ...`.

[clutch]: https://github.com/logsem/clutch

Upstream source: `~/Desktop/clutch/clutch-logsem/theories/<subdir>/<file>.v`
(clutch-logsem checkout, commit not pinned — update the table below when you
re-sync).

The Coq namespace mapping:

```
-Q src/eris eris            ← clutch/theories/ upstream, renamed
-Q src/discprob discprob    ← clutch/external/proba/ upstream
```

## Files copied from `clutch-logsem/theories/`

| Relative path in this repo | Upstream path | Notes |
| --- | --- | --- |
| `src/eris/prelude/base.v` | `theories/prelude/base.v` | |
| `src/eris/prelude/classical.v` | `theories/prelude/classical.v` | |
| `src/eris/prelude/tactics.v` | `theories/prelude/tactics.v` | |
| `src/eris/prelude/stdpp_ext.v` | `theories/prelude/stdpp_ext.v` | |
| `src/eris/prelude/mc_stdlib.v` | `theories/prelude/mc_stdlib.v` | |
| `src/eris/prelude/asubst.v` | `theories/prelude/asubst.v` | Autosubst helpers |
| `src/eris/prelude/iris_ext.v` | `theories/prelude/iris_ext.v` | |
| `src/eris/prelude/fin.v` | `theories/prelude/fin.v` | |
| `src/eris/prelude/fiber_bounds.v` | `theories/prelude/fiber_bounds.v` | |
| `src/eris/prelude/Coquelicot_ext.v` | `theories/prelude/Coquelicot_ext.v` | Coquelicot extensions |
| `src/eris/prelude/Reals_ext.v` | `theories/prelude/Reals_ext.v` | |
| `src/eris/prelude/Series_ext.v` | `theories/prelude/Series_ext.v` | |
| `src/eris/prelude/NNRbar.v` | `theories/prelude/NNRbar.v` | non-neg extended reals |
| `src/eris/prelude/properness.v` | `theories/prelude/properness.v` | |
| `src/eris/prelude/uniform_list.v` | `theories/prelude/uniform_list.v` | |
| `src/eris/prelude/zmodp_fin.v` | `theories/prelude/zmodp_fin.v` | mathcomp fin ↔ Z/nZ |
| `src/eris/prob/countable_sum.v` | `theories/prob/countable_sum.v` | `SeriesC` |
| `src/eris/prob/distribution.v` | `theories/prob/distribution.v` | `distr`, `dret`, `dbind`, `dmap`, `dunif`, … |
| `src/eris/prob/couplings.v` | `theories/prob/couplings.v` | probabilistic couplings |
| `src/eris/prob/couplings_app.v` | `theories/prob/couplings_app.v` | approximate couplings |
| `src/eris/prob/couplings_exp.v` | `theories/prob/couplings_exp.v` | expectation couplings |
| `src/eris/prob/couplings_dp.v` | `theories/prob/couplings_dp.v` | differential-privacy couplings |
| `src/eris/prob/markov.v` | `theories/prob/markov.v` | |
| `src/eris/prob/mdp.v` | `theories/prob/mdp.v` | |
| `src/eris/prob/generic_lifting.v` | `theories/prob/generic_lifting.v` | |
| `src/eris/prob/graded_predicate_lifting.v` | `theories/prob/graded_predicate_lifting.v` | `glm` monad — used by eris's WP |
| `src/eris/common/locations.v` | `theories/common/locations.v` | |
| `src/eris/common/language.v` | `theories/common/language.v` | generic probabilistic language |
| `src/eris/common/ectx_language.v` | `theories/common/ectx_language.v` | |
| `src/eris/common/ectxi_language.v` | `theories/common/ectxi_language.v` | |
| `src/eris/common/exec.v` | `theories/common/exec.v` | |
| `src/eris/common/erasable.v` | `theories/common/erasable.v` | |
| `src/eris/bi/weakestpre.v` | `theories/bi/weakestpre.v` | generic WP base |
| `src/eris/base_logic/error_credits.v` | `theories/base_logic/error_credits.v` | `ecGS`, `↯ ε`, `ec_supply`, `ec_split`, `ec_zero`, `ec_contradict` |
| `src/eris/eris/weakestpre.v` | `theories/eris/weakestpre.v` | **`erisWpGS`**, `pgl_wp`, `glm`-based WP definition |
| `src/eris/eris/lifting.v` | `theories/eris/lifting.v` | `wp_lift_step_fupd_glm`, `wp_lift_step_fupd`, … |
| `src/eris/eris/ectx_lifting.v` | `theories/eris/ectx_lifting.v` | `wp_lift_head_step_fupd_couple`, `wp_lift_atomic_head_step`, … |

## Files copied from `clutch-logsem/external/proba/`

This is an external dependency of clutch (discrete-probability kernels
used under the `discprob` namespace inside clutch's prelude/Series_ext.v
and prelude/fiber_bounds.v).

| Relative path | Upstream path |
| --- | --- |
| `src/discprob/basic/base.v` | `external/proba/basic/base.v` |
| `src/discprob/basic/nify.v` | `external/proba/basic/nify.v` |
| `src/discprob/basic/order.v` | `external/proba/basic/order.v` |
| `src/discprob/basic/classic_proof_irrel.v` | `external/proba/basic/classic_proof_irrel.v` |
| `src/discprob/basic/sval.v` | `external/proba/basic/sval.v` |
| `src/discprob/basic/seq_ext.v` | `external/proba/basic/seq_ext.v` |
| `src/discprob/basic/stdpp_ext.v` | `external/proba/basic/stdpp_ext.v` |
| `src/discprob/basic/bigop_ext.v` | `external/proba/basic/bigop_ext.v` |
| `src/discprob/basic/exp_ext.v` | `external/proba/basic/exp_ext.v` |
| `src/discprob/basic/monad.v` | `external/proba/basic/monad.v` |
| `src/discprob/basic/Reals_ext.v` | `external/proba/basic/Reals_ext.v` |
| `src/discprob/basic/Series_Ext.v` | `external/proba/basic/Series_Ext.v` |
| `src/discprob/prob/countable.v` | `external/proba/prob/countable.v` |
| `src/discprob/prob/double.v` | `external/proba/prob/double.v` |
| `src/discprob/prob/rearrange.v` | `external/proba/prob/rearrange.v` |

## Intentionally not copied from clutch-logsem

- `theories/prob_lang/*` — clutch's specific probabilistic heap-lang.
  We have our own language (λRust-based), so we don't need it.
- `theories/eris/primitive_laws.v`, `theories/eris/adequacy.v`,
  `theories/eris/error_rules.v`, `theories/eris/proofmode.v` — all are
  written against `prob_lang`. We write our own at
  `src/lambda_verus/lang/` targeting `lrust_lang`.
- `theories/eris/total_*` — total WP variants; not needed for partial WP.
- `theories/{caliper,tachis,approxis,coneris,con_prob_lang,delay_prob_lang,meas_lang,diffpriv,elton,foxtrot,musketeer_dp,pure_complete,selfcomp,clutch}` —
  other probabilistic logics in the clutch family (refinement, higher-order,
  concurrent, continuous, …). None of them are needed for eris-style
  sequential error-credit reasoning.
- `theories/prob/monad/*` — measure-theoretic probability monad; the
  discrete `distribution.v` is enough for our use.
- `theories/prob/differential_privacy.v`, `theories/prob/couplings_kanto.v`,
  `theories/common/con_*.v`, `theories/common/sch_erasable.v`,
  `theories/common/inject.v` — DP-specific, concurrent-specific, or pull
  in `prob_lang`.
- `theories/base_logic/spec_{auth_markov,update}.v`,
  `theories/base_logic/error_credits_mult.v` — spec-refinement and
  multiplicative-error variants, not needed for eris.

## Re-syncing

When updating to a newer clutch commit:

1. In `~/Desktop/clutch/clutch-logsem/`, `git pull` and `make`.
2. Re-run the same `cp -R` commands used to seed this tree — see
   `git log --all --oneline src/eris` for the exact invocation of
   the initial vendoring commit.
3. Delete generated `*.vo`, `*.vok`, `*.vos`, `*.glob`, `*.aux` from
   `src/eris/` and `src/discprob/`.
4. `make` from the repo root; if new transitive deps appear (new
   imports inside the already-copied files), copy those across too and
   add them to `_CoqProject` / `_RocqProject`.
5. Update this document's table.

## Opam dependencies required by the vendored code

(Already installed in the `clutch` opam switch, as of this vendoring.)

- `coq-coquelicot` (real analysis)
- `coq-mathcomp-ssreflect`, `coq-mathcomp-solvable`, `coq-mathcomp-analysis`,
  `coq-mathcomp-algebra`, `coq-mathcomp-field`, `coq-mathcomp-fingroup`,
  `coq-mathcomp-classical`, `coq-mathcomp-reals` (ssreflect + analysis)
- `coq-mathcomp-bigenough`, `coq-mathcomp-finmap` (indirectly)
- `coq-autosubst` (substitutions, via `asubst.v`)
- `coq-hierarchy-builder` (HB-style structures)
- `rocq-iris` (>= 4.5.0)
- `rocq-stdpp` (>= 1.13.0)
