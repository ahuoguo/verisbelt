(** Thin wrapper over iris's adequacy.

    Previously this file carried a customized [wp_strong_adequacy_gen]
    that pre-allocated [£k] credits for the caller. After the iris MR
    !1171 port (hfupd-based adequacy), we use iris's stock adequacy
    directly — callers that need extra credits should allocate them via
    [num_laters_per_step] at step 0. *)
From iris.program_logic Require Export language weakestpre adequacy.
