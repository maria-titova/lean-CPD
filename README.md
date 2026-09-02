# Coalition-Proof Disclosure

Lean 4 formalization accompanying the paper **“Coalition-Proof Disclosure”** by Germán Gieczewski and Maria Titova.

## Acknowledgments

This formalization was developed with assistance from Aristotle by Harmonic, Claude Opus 4.8, Claude Fable 5, and GPT-5.6-Sol.

The library is self-contained apart from mathlib and one explicitly declared mathematical axiom: Kakutani’s fixed-point theorem for finite-dimensional real normed spaces. The root module is `CPD.lean`; source modules are in `CPD/`.

## Build

The Lean toolchain and mathlib revision are pinned by `lean-toolchain` and `lake-manifest.json`.

```sh
lake exe cache get
lake build
```

Build outside folders managed by file-synchronization software. For example, copy the repository to a temporary local directory before running Lake.

## Axiom policy

`CPD/Kakutani.lean` declares `CPD.kakutani`, because Kakutani’s fixed-point theorem is not currently available in mathlib. It is used by `DisclosureGame.exists_PBE` in `CPD/PBEExistence.lean`. Results that invoke PBE existence therefore depend on this axiom. All other dependencies are mathlib’s foundational axioms.

The source contains no `sorry` or `admit` declarations.

## Library organization

- `Simplex`, `Game`, `Strategy`, and `Restriction` define the model; `BestResponse`
  proves its best-response microfoundation.
- `Coalition` and `Partition` define coalitions, residual games, partitions, and associated strategies.
- `Feasible`, `PBE`, `PBEExistence`, and `PBEChar` develop perfect Bayesian equilibrium.
- `CoalitionPayoffs`, `CoalitionProof`, `COE`, and `LexMax` develop coalition-proofness, greedy partitions, coalition-optimal partitions, and lexicographic maximality.
- `Existence`, `Theorem1`, `GreedyPrefix`, `Betweenness`, `BetweennessCore`, `Theorem2`, `BetweennessGeneric`, and `BetweennessOrder` prove the quasiconcavity and betweenness existence results.
- `CheapTalk` and `Theorem4` prove the cheap-talk results.
- `Degrading` and `ExistenceDegrading` prove the payoff-degradation results.
- `Tightness` proves non-existence and two-type existence.
- `SelfEnforcing` treats self-enforcing blocking coalitions.
- `RichGame` and `TentPath` formalize rich disclosure games and the tent function.
- `EvidenceGame` and `HKPGeneric` formalize the comparison with truth-leaning equilibrium.

## Paper correspondence

“Kakutani” marks results whose proofs use `CPD.kakutani`. Files are relative to `CPD/`.

| Paper item | Lean declaration(s) | File | Axioms |
|---|---|---|---|
| Assumption 1 and Definition 1 | `DisclosureGame` | `Game.lean` | mathlib |
| Envelope properties | `vbar_mem`, `vlow_mem`, `V_eq_Icc`, `vbar_upperSemicontinuousOn`, `vlow_lowerSemicontinuousOn` | `Game.lean` | mathlib |
| Definition 2 | `Coalition` | `Coalition.lean` | mathlib |
| Remark 1 | `exists_coalition` | `Coalition.lean` | mathlib |
| Definitions 3–4 and Remark 2 | `Partition`, `partitionStrategy`, `exists_partition`, `card_le` | `Partition.lean` | mathlib |
| Definition 5 | `feasibleBeliefs` | `Feasible.lean` | mathlib |
| Definition 6 | `skeptical`, `skeptical_isWellDefined` | `Feasible.lean` | mathlib |
| Definition 7 | `Supports`, `IsPBE` | `PBE.lean` | mathlib |
| Definition 8 | `IsIR`, `IsPBEPartition` | `PBEChar.lean` | mathlib |
| Lemma 1 | `isIR_iff_sup_le` | `PBEChar.lean` | mathlib |
| Proposition 1 | `pbe_characterization` | `PBEChar.lean` | mathlib |
| Definition 9 | `BlockingCoalition`, `IsCoalitionProof` | `CoalitionProof.lean` | mathlib |
| Definition 10 | `IsGreedy` | `CoalitionProof.lean` | mathlib |
| Proposition 2 | `cppbe_characterization`, `isCPPBEStrategy_iff_associated_greedy` | `CoalitionProof.lean` | mathlib |
| Definition 11 | `IsLexMax` (a strengthening; see the module documentation) | `LexMax.lean` | mathlib |
| Proposition 3 | `lexmax_exists` (Kakutani); `isLexMax_of_isCPPBE`, `cppbe_iff_lexmax_cp` (mathlib) | `LexMax.lean` | mixed |
| Definition 12 | `Generic` | `Existence.lean` | mathlib |
| Definitions 13–14 | `QC`, `QCStar`, `MC` | `Existence.lean` | mathlib |
| Lemma 2 | `isCompact_coalitionPayoffs` | `CoalitionPayoffs.lean` | mathlib |
| Lemma 3 | `pooling_dominance`, `isGreatest_coalitionPayoffs_iff`, `coalition_attains_max` | `Existence.lean` | mathlib |
| Theorem 1 | `one_existence`, `one_noHalt`, `one_noHalt_full`, `one_unique` | `Theorem1.lean`, `GreedyPrefix.lean` | mathlib |
| Definition 15 | `SingleValued`, `Betweenness`, `StrictBetweenness` | `BetweennessCore.lean`, `Betweenness.lean` | mathlib |
| Lemma 4 | `value_id` | `BetweennessCore.lean` | mathlib |
| Lemma 5 | `vstar`, `vstar_isGreatest`, `btw_attained` | `BetweennessCore.lean` | Kakutani |
| Lemma 6 | `btw_merging`, `btw_merging_impossible` | `BetweennessCore.lean` | Kakutani |
| Theorem 2, strict-betweenness branch | `two_noHalt_full`, `two_existence`, `bstar_cppbe_iff_coe`, `two_unique` | `Theorem2.lean` | Kakutani |
| Theorem 2, genericity branch | `btw_generic_noHalt`, `btw_generic_existence`, `btw_generic_cppbe_iff_coe`, `btw_generic_unique` | `BetweennessGeneric.lean` | Kakutani |
| Theorem 3 | `three_existence` | `BetweennessOrder.lean` | Kakutani |
| Definition 16 | `MCT` | `CheapTalk.lean` | mathlib |
| Definition 17 | `qcClosure` | `CheapTalk.lean` | mathlib |
| Theorem 4 and Corollary 1 | `four_existence`, `pure_ct` | `Theorem4.lean` | mathlib |
| Definition 18 and Theorem 5 | `DegradationProperty`, `degrade_halts`, `degrade_noHalt_full` | `Degrading.lean`, `GreedyPrefix.lean` | mathlib |
| Definitions 19–21 | `FreeDisposal`, `Degradable`, `RevelationAverse` | `Degrading.lean` | mathlib |
| Proposition 4 | `degrade_general`, `free_disposal_existence`, `ra_degradable_existence` | `Degrading.lean`, `ExistenceDegrading.lean` | mathlib |
| Proposition 5 | `nonexistence`, `nonexistence_mct` | `Tightness.lean` | mathlib |
| Theorem 6 | `binary_existence` | `Tightness.lean` | mathlib |
| Definition 22 and Proposition 6 | `BlockingCoalition.SelfEnforcing`; `cppbe_iff_no_selfEnforcing_qcstar`, `cppbe_iff_no_selfEnforcing_generic` (mathlib); `cppbe_iff_no_selfEnforcing_bstar` (Kakutani) | `SelfEnforcing.lean` | mixed |
| Definitions 23–24, Lemma I.1, and Proposition 7 | `RichGame`, `CoalitionOptimalPartition`, `attainability`, `cutecase_existence`, `cutecase_unique` | `RichGame.lean` | mathlib |
| Definition 25, Lemma I.2, and Proposition 8 | `NestedChain`, `SimplexDecomp`, `simplexDecomp_exists`, `faceMax_peak_consistency`, `tent_path_independence` | `RichGame.lean`, `TentPath.lean` | mathlib |
| Definition 26 and Proposition 9 | `tent`, `tent_eq_at_faceMax`, `tent_affine_on_chain`, `tent_unique` | `RichGame.lean` | mathlib |
| Definitions 27–28 and Proposition 10 | `EvidenceStructure`, `TruthLeaningSupports`, `hkp_dichotomy`, `hkp_cppbe` | `EvidenceGame.lean` | mathlib |
| Corollary 2 | `hkp_generic` | `HKPGeneric.lean` | Kakutani |
| Lemma B.1 | `blocking_on_path` | `CoalitionProof.lean` | mathlib |
| Lemma C.1, Definition C.1, and Lemma C.2 | `isGreatest_stepMax`, `greedyLower_le_stepMax`, `IsCOE`, `IsCOE.isGreedy`, `isCOE_iff_of_greedy` | `COE.lean` | mathlib |
| Lemma D.1 | `merging` | `Existence.lean` | mathlib |
| Lemma E.1 | `btw_order`, with `btw_order_aux` and `proper_separation` | `BetweennessOrder.lean`, `BetweennessRank.lean` | mathlib |
| Lemmas F.1–F.3 | `closureGame`, `closureGame_QC`, `closureGame_MC`, `coalition_w_le_qcClosure`, `ct_realization` | `CheapTalk.lean` | mathlib |
| Lemma K.1 | `bestResponse_payoff_correspondence`, with `senderPayoffCorr_eq_convexHull` and the component best-response, envelope, and correspondence results | `BestResponse.lean` | mathlib |
| Lemma K.2 | `restrict`, `restrict_self`, `restrict_restrict` | `Restriction.lean` | mathlib |
| Lemma K.3 | `feasibleBeliefs_eq_polytope`, compactness and convexity lemmas | `Feasible.lean` | mathlib |
| Lemma K.4 | `exists_PBE` | `PBEExistence.lean` | Kakutani |
