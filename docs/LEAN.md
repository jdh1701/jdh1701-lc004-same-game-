# The Lean library

Toolchain `leanprover/lean4:v4.19.0`, Mathlib `v4.19.0`. There are 251 modules in `LC004/`, every one reachable from `LC004.lean`. The source guard rejects `sorry`, custom axioms, and `unsafe` or `partial` code. The axiom audit, `scripts/AxiomAudit.lean`, permits only `propext`, `Classical.choice` and `Quot.sound`.

## Entry points

| Theorem | Module | Meaning |
|---|---|---|
| `raw_max_win_iff_certificate` | `RawCertificateEquivalence` | Winning ⇔ a noncrossing certificate of blocks of size 2 and 3 exists |
| `winningColorPatternCount_second_diagonal` | `SecondDiagonalClosedForm` | A(2k+2,k) = k·C(2k+2,k−1) |
| `winning_iff_heavy_face_decomposition` | `HeavyFaceDecomposition` | The face lemma |
| `winningJoinCoefficient_ne_zero_crossed_class_card_ge_five` | `CrossedClassMinSize` | A crossed class with nonzero coefficient has size ≥ 5 |
| `raw_max_win_iff_fusionEval`, `raw_max_win_iff_fusionReach` | `FusionStack` | Fusion-automaton semantics of the original game |

## Adding a module

1. Put it in `LC004/` and import it from `LC004.lean`. `scripts/check_lean_coverage.py` fails on an orphan module.
2. Push a branch and open a PR. `lean.yml` builds the library, runs the coverage check and the source guard, and runs the axiom audit.
3. Promote the claim to PROVED-LEAN in the WORKBOARD only after a green run on the exact head commit. Cite the run ID.

## All modules

Theorem and lemma counts come from a text scan of each file.

| Module | Theorems | Module doc (first line) |
|---|---|---|
| `AdjacentContraction` | 15 |  |
| `AdjacentInflationKernel` | 7 |  |
| `BlockCrossingInsertion` | 3 |  |
| `BoundaryContextRegression` | 1 |  |
| `BoundaryLemmas` | 5 |  |
| `Bridge` | 3 |  |
| `BridgeAdjacentBoundary` | 1 |  |
| `BridgeAdjacentLeft` | 1 |  |
| `BridgeAdjacentLeftClosure` | 1 |  |
| `BridgeAdjacentLeftConcrete` | 1 |  |
| `BridgeAdjacentLeftFront` | 0 |  |
| `BridgeAdjacentPrefixTransport` | 1 |  |
| `BridgeExchangeAssembly` | 2 |  |
| `BridgeExchangeFarLeft` | 1 |  |
| `BridgeExchangeLeftAssembly` | 1 |  |
| `BridgeExchangeRemaining` | 1 |  |
| `BridgeExchangeRight` | 4 |  |
| `BridgeExchangeRightFull` | 1 |  |
| `BridgeFarLeftConcrete` | 1 |  |
| `BridgeFarLeftProof` | 2 |  |
| `BridgeStructuralFinal` | 3 |  |
| `CertificateConstraintJoins` | 3 |  |
| `CertificateConverse` | 5 |  |
| `CertificateDeletion` | 3 |  |
| `CertificateFirstErase` | 2 |  |
| `CertificateInsertion` | 1 |  |
| `CertificateJoinIteration` | 3 |  |
| `CertificatePairRefinement` | 6 |  |
| `CertificatePairRegions` | 5 |  |
| `ChoiceAbstractCancellation` | 7 |  |
| `ChoiceBijectiveQuotient` | 12 |  |
| `ChoiceBinaryClosure` | 2 |  |
| `ChoiceBoundaryClassification` | 8 |  |
| `ChoiceComplexCancellation` | 9 |  |
| `ChoiceCoordinateReduction` | 9 |  |
| `ChoiceFunctionalElimination` | 3 |  |
| `ChoiceImplicationRecognition` | 3 |  |
| `ChoiceQuotientFaceSum` | 9 |  |
| `ChoiceReducedCancellation` | 8 |  |
| `ChoiceRelationClassification` | 5 |  |
| `ChoiceSupportedCancellation` | 11 |  |
| `ChoiceSupportedDomains` | 15 |  |
| `ChoiceUniversalValue` | 6 |  |
| `ClassCutSeparators` | 4 |  |
| `CollectedJoinCoefficients` | 3 |  |
| `ColorPatternSpace` | 11 |  |
| `CommonCertificateGap` | 8 |  |
| `ConditionalGrammarBridge` | 2 |  |
| `ConditionalInsertion` | 3 |  |
| `ConditionalMain` | 2 |  |
| `ConnectedClassCrossing` | 3 |  |
| `ConnectedCoefficientInterpolation` | 5 |  |
| `ConnectedCoefficientSupport` | 13 |  |
| `ConnectedFirstExcess` | 4 |  |
| `CrossedClassMinSize` | 2 |  |
| `CrossedFourCancellation` | 3 |  |
| `CyclicRootLemma` | 6 |  |
| `CyclicWordEnumeration` | 5 |  |
| `DegreePrefixArithmetic` | 5 |  |
| `DeleteSimulation` | 1 |  |
| `DoubleExceptionalWordCount` | 4 |  |
| `DoubleFiberCountCorrespondence` | 3 |  |
| `DoubleFiberGeometry` | 6 |  |
| `DoubleRepresentationCount` | 2 |  |
| `EncodingAgreement` | 1 |  |
| `EndpointMatching` | 5 |  |
| `EndpointMatchingDyck` | 4 |  |
| `ErasureColorSymmetry` | 3 |  |
| `ExceptionalDegreeProfiles` | 5 |  |
| `ExchangeDominance` | 5 |  |
| `ExchangeScaffold` | 7 |  |
| `ExchangeTarget` | 2 |  |
| `ExclusiveSeparatorElimination` | 6 |  |
| `ExecutableCorrespondence` | 6 |  |
| `ExecutableStep` | 1 |  |
| `ExecutableUniqueness` | 6 |  |
| `FaceBoundaryJoinPrelim` | 2 |  |
| `FaceInternalPaths` | 1 |  |
| `FaceJoinConditional` | 2 |  |
| `FaceJoinOrder` | 3 |  |
| `FaceJoinPaths` | 3 |  |
| `FacePathFactorization` | 2 |  |
| `FaceRestriction` | 2 |  |
| `FinalAssembly` | 2 |  |
| `FiniteIncidenceSupport` | 4 |  |
| `FiveCertificateGeneratorEquiv` | 4 |  |
| `FiveClassActualGeometry` | 3 |  |
| `FiveClassFiniteGeometry` | 10 |  |
| `FiveClassGeometryApplication` | 5 |  |
| `FiveClassGeometryBridge` | 6 |  |
| `FiveClassGeometryCases0` | 85 |  |
| `FiveClassGeometryCases1` | 85 |  |
| `FiveClassGeometryCases2` | 85 |  |
| `FiveClassGeometryCases3` | 85 |  |
| `FiveClassGeometryCases4` | 85 |  |
| `FiveClassGeometryCases5` | 85 |  |
| `FiveClassGeometryExhaustive` | 3 |  |
| `FiveClassLocalRefinement` | 3 |  |
| `FiveClassRankNormalization` | 4 |  |
| `FiveClassRefinementEquiv` | 5 |  |
| `FiveClassSeparatorElimination` | 14 |  |
| `FiveClassSeparators` | 9 |  |
| `FiveClassSplitCancellation` | 4 |  |
| `FiveClassSplitJoins` | 6 |  |
| `FiveClassSplitPartitions` | 8 |  |
| `FiveClassSurvivorRecognition` | 5 |  |
| `FiveCoefficientChoiceBridge` | 4 |  |
| `FiveCoordinateGeometry` | 6 |  |
| `FiveEncodedBlocks` | 4 |  |
| `FiveOriginalCoefficientLaw` | 6 |  |
| `FivePatternCoordinates` | 9 |  |
| `FourBlockCrossing` | 1 |  |
| `FourBlockOverlapCorollary` | 1 |  |
| `FourClassLocalPairs` | 2 |  |
| `FourClassTwoShapes` | 4 |  |
| `FourGapAssembly` | 4 |  |
| `FourGapCoefficientSupport` | 5 |  |
| `FourGapIndicator` | 2 |  |
| `FourGapRefinementIndicator` | 3 |  |
| `FourGapWitnessOverlap` | 5 |  |
| `FourGeneratorPositiveCoefficient` | 1 |  |
| `FourRefinementOverlap` | 8 |  |
| `FourfoldCertificatePairs` | 5 |  |
| `FourfoldDoubleFiber` | 1 |  |
| `FourfoldFiberCount` | 8 |  |
| `FourfoldMatchingChoices` | 6 |  |
| `FourfoldRepresentationSurjection` | 7 |  |
| `FourfoldSplit` | 8 |  |
| `FreeIntervalElimination` | 4 |  |
| `FullRunErasure` | 1 |  |
| `FullSimulation` | 2 |  |
| `FusionHorizon` | 5 |  |
| `FusionStack` | 20 |  |
| `GrammarColorSymmetry` | 1 |  |
| `GrammarErase` | 6 |  |
| `GrammarLength` | 4 |  |
| `HeadColorLemmas` | 3 |  |
| `HeavierLemmas` | 2 |  |
| `HeavyFaceCertificateProduct` | 5 |  |
| `HeavyFaceDecomposition` | 9 |  |
| `HeavyFaceReconstruction` | 3 |  |
| `HeavyFaceRestriction` | 4 |  |
| `HistoryCertificate` | 8 |  |
| `IncidenceFaceSum` | 7 |  |
| `IndexedDeterminism` | 2 |  |
| `IndexedMove` | 6 |  |
| `InnermostBlock` | 7 |  |
| `InsertedDeletion` | 1 |  |
| `InsertionRunCases` | 3 |  |
| `InteriorNoMerge` | 1 |  |
| `IntrinsicDiagonalProfiles` | 11 |  |
| `JoinRigidBlocks` | 5 |  |
| `LabeledConnectedExpansion` | 3 |  |
| `LabeledJoinEnumeration` | 4 |  |
| `ListSplit` | 1 |  |
| `LocalCertificateCatalogues` | 8 |  |
| `LocalGeneratorTransfer` | 3 |  |
| `MatchingCatalan` | 5 |  |
| `MatchingDyckEncoding` | 8 |  |
| `MatchingDyckInjective` | 6 |  |
| `MatchingMergeProfile` | 8 |  |
| `MatchingPartner` | 6 |  |
| `MatchingPatternMerge` | 3 |  |
| `MatchingRepresentationCardinality` | 6 |  |
| `MixedFiveSixCertificates` | 5 |  |
| `MixedFiveSixCoefficient` | 11 |  |
| `MixedFiveSixGeometry` | 14 |  |
| `Monotonicity` | 1 |  |
| `MoveClassification` | 4 |  |
| `NewProofAxiomAudit` | 0 | This is a reproducible Lean compiler audit, not a statement of publication |
| `NoMergeAdjacentLeft` | 0 |  |
| `NoMergeAdjacentLeftBoundary` | 1 |  |
| `NoMergeAdjacentLeftBoundaryConcrete` | 1 |  |
| `NoMergeAdjacentLeftConcrete` | 1 |  |
| `NoMergeAdjacentRight` | 1 |  |
| `NoMergeExchangeAssembly` | 3 |  |
| `NoMergeExchangeInterior` | 0 |  |
| `NoMergeExchangeLocal` | 2 |  |
| `NoMergeExchangeRight` | 2 |  |
| `NoMergeFarLeftProof` | 1 |  |
| `NoMergeFarRightProof` | 1 |  |
| `NoMergeFarRightZero` | 2 |  |
| `NoMergeFull` | 1 |  |
| `NoMergeSimulation` | 2 |  |
| `NoMergeStructuralProof` | 3 |  |
| `NoncrossingBlockFamily` | 5 |  |
| `NoncrossingClosure` | 9 |  |
| `NoncrossingClosureRegions` | 5 |  |
| `NoncrossingCoefficientProduct` | 3 |  |
| `NoncrossingCoefficientPushforward` | 5 |  |
| `NoncrossingConnectedFiber` | 1 |  |
| `NoncrossingDegreeInjective` | 3 |  |
| `NoncrossingDegreeRealization` | 2 |  |
| `NoncrossingDegreeWordEquiv` | 6 |  |
| `NoncrossingInsertionIndex` | 4 |  |
| `NoncrossingLastBlock` | 9 |  |
| `NoncrossingProfileEnumeration` | 1 |  |
| `NoncrossingRegionEquivalence` | 2 |  |
| `NoncrossingRegionPatternEquiv` | 7 |  |
| `Normalized` | 2 |  |
| `NormalizedDirectional` | 4 |  |
| `NormalizedStepTarget` | 1 |  |
| `OrderedCertificateAssembly` | 4 |  |
| `PairFamilyInsertion` | 2 |  |
| `PairPatternCertificate` | 7 |  |
| `PartitionExceptionalWordProfiles` | 6 |  |
| `PartitionIntervalDegrees` | 9 |  |
| `PartitionIntervalInsertion` | 9 |  |
| `PartitionOpeningMass` | 15 |  |
| `PatternCoarseningCorrespondence` | 3 |  |
| `PrefixIndexed` | 5 |  |
| `ProductIncidence` | 4 |  |
| `RawAnywhereHeaviness` | 4 |  |
| `RawAnywhereRepeat` | 1 |  |
| `RawCertificateEquivalence` | 8 |  |
| `RawEncoding` | 2 |  |
| `RawIsolatedInsertion` | 3 |  |
| `RawMaxSemanticsBridge` | 3 |  |
| `RawPrefixHeaviness` | 2 |  |
| `RawPrefixRepeat` | 1 |  |
| `RawRunInflation` | 10 |  |
| `RegionalClassCount` | 4 |  |
| `ReverseInsertionHistory` | 5 |  |
| `RigidFaceArcCriterion` | 1 |  |
| `RigidFaceGeometry` | 11 |  |
| `RunEncoding` | 2 |  |
| `RunLengthTwoThree` | 2 |  |
| `RunState` | 2 |  |
| `SecondDiagonalArithmetic` | 5 |  |
| `SecondDiagonalClosedForm` | 5 |  |
| `SecondDiagonalCountAssembly` | 3 |  |
| `SecondDiagonalEndpoint` | 3 |  |
| `SecondDiagonalProfiles` | 6 |  |
| `SeparatorDeletionLink` | 9 |  |
| `Simulation` | 1 |  |
| `SingleExceptionalWordCount` | 3 |  |
| `SixBoundaryLists` | 8 |  |
| `SixClassSeparatorFacets` | 10 |  |
| `SmallGeneratorCoefficients` | 2 |  |
| `SmallPatternCorrespondence` | 8 |  |
| `SmallRefinementGap` | 7 |  |
| `SplitRunLemmas` | 1 |  |
| `SuccessfulPaths` | 10 |  |
| `SuffixIndexed` | 2 |  |
| `Transition` | 0 |  |
| `TwoTripleCorrespondence` | 3 |  |
| `TypedInsertionPositions` | 5 |  |
| `UnconditionalFinal` | 2 |  |
| `WeightedConnectedFibers` | 4 |  |
| `WinningConstraintGenerators` | 4 |  |
| `WinningJoinCount` | 3 |  |
