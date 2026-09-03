# Certified inventory — `formal/POFreeLift.lean`

> ## ⚠ STALE — generated 2026-08-20, before the pivot
>
> This inventory predates the cone-scheme route and does **not** list its
> declarations. Figures below are from 2026-08-20 (1,036 top-level
> declarations); the file now has **2,362**, still 0 sorries and 0 warnings.
>
> **The capstones it is missing**, all in `formal/POFreeLift.lean`:
> `decidableFSat` (raw input, with `nnfP_correct`), `decidableSat_cone` (NNF),
> `decidableSetSat` (concrete sets), `satisfiable_iff_set` (abstract $=$
> concrete, no fragment hypothesis), `coneScheme_sound`, `coneScheme_complete`,
> `coneScheme_unsat_full`, and the control layer `sigStatic` / `compatB` /
> `pruneSig` / `gfpIter`. Provenance: `ASSEMBLY_DESIGN.md` §§267–297.
>
> Everything listed below still exists and is still proved — the risk this file
> guards against (re-deriving what exists) is unchanged for those entries. The
> risk it now *adds* is treating its omissions as absences.

Generated 2026-08-20. **Purpose: stop re-deriving what already exists.** Twice in
one session I treated certified machinery as absent (the two certificate
architectures of §40; the whole step-5 encoding pipeline), and each cost real
work. Consult this before designing anything.

File: 1,036 top-level declarations, 364 with `#print axioms`, 0 sorries, 0 warnings.

This also serves the eventual SLIMMING: the core needed for the fragment's
decidability is a small subset of the below, and the rest is scaffolding,
superseded routes, or witnesses.

## DECIDABILITY RESULTS (the actual goals reached)

- `decidableSat_Calt`
- `decidableSat_Ccar`
- `decidableSat_Cdesc`
- `decidableSat_Clin_rr`
- `decidableSat_Cmix`
- `decidableSat_Cvert`
- `decidableSat_hfrag`
- `decidableSat_of_codes`
- `decidableSat_vtower`
- `decidableSat_vtowerG`
- `decidableSat_vtowerRR`
- `decidableSat_vtowerRRI`
- `satisfiable_iff_allfree_cert`
- `satisfiable_iff_hfrag_cert`
- `satisfiable_iff_podr_cert`

## SOUNDNESS CORE (certificate -> model)

- `multiTier_hintikka`
- `multiTier_sound`
- `munf_is_frame`
- `sat_from_hintikka_frame`
- `truth_lemma`
- `twoTier_sound`

## FRAMES (what a certificate may declare)

- `frame_q_of_odNet`
- `glueFam_frame`
- `odNet_frame`
- `po_default_multi_frame`
- `po_dr_multi_kernel_frame`
- `posetNet_frame`
- `qnet_odNet`
- `readoff_qnet_frame`
- `symDrPo_frame`

## CERTIFICATE VALIDITY (MultiTierOk producers)

- `glueFam_ok`
- `mixKernelsV_ok`
- `mixKernels_ok`
- `mixKernels_pool_ok`
- `mtkKernelsDR_ok`
- `mtkKernelsDir_ok`
- `mtkKernels_ok`
- `posetKernel_ok`
- `posetMT_ok`
- `vkernel2_ok`
- `vkernel_ok`
- `vtowers_ok`

## FINITENESS / ENCODING / codes (step 5 machinery)

- `codes`
- `codesV`
- `decidableSat_of_codes`
- `encodeHF_mem_codes`
- `mtAcceptB_sound`
- `mtOkB_iff`
- `mtkBound`
- `mtkNodes_length_le`

## EXTRACTION -- vertical (towers, merge, selection)

- `class_kernel`
- `class_persistAll`
- `class_tower`
- `classify_cross`
- `exists_bank`
- `exists_bank_ppi`
- `exists_maximal_tower`
- `exists_stable_base`
- `family_hrectQ`
- `family_range`
- `kernel_range_of_persistAll`
- `merge_sites`
- `mixSelect_assembled`
- `persistAll_merge2`
- `rr_covers`
- `rr_segment_from`
- `towers_from_persistPP`
- `vtowers_merged`

## MODEL-SIDE ANALYSIS (stabilisation, forcing)

- `backward_forcing_dr`
- `backward_forcing_pp`
- `external_stabilizes`
- `externals_stabilize`
- `forward_absorption_ppi`
- `mty_no_all_po`
- `po_up`
- `pofree_cl_all`
- `rank_eq_imp_value_eq`
- `recurrent_tail`
- `row_no_return`
- `segment_exists_bounded`
