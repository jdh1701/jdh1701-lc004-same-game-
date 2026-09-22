import LC004.Normalized
import LC004.ExchangeScaffold
import LC004.SuccessfulPaths

namespace LC004

/-- The concrete no-merge exchange law needed by the final induction. -/
def NormalizedNoMergeExchange : Prop :=
  ∀ {s : RunState} {ch : Nat × RunState},
    Normalized s →
    NoMergeChoice s ch →
    SuccessfulChoice s ch →
    ChildChoicesLift s ch

/-- The concrete bridge exchange law needed by the final induction. -/
def NormalizedBridgeExchange : Prop :=
  ∀ {pre post : RunState} {c d : Nat} {bp bq : Bool},
    Normalized
      (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post) →
    BridgeChildChoicesLiftExceptMerged pre post c d bp bq

/-- Conditional hard direction. Once the two local exchange laws are supplied,
there is no further Same-Game-specific gap: a normalized nonempty state with a
unique successful first indexed choice has a unique complete successful path. -/
theorem uniqueCompletePath_of_uniqueSuccessfulChoice_exchange
    (hno : NormalizedNoMergeExchange)
    (hbridge : NormalizedBridgeExchange)
    {s : RunState}
    (hn : Normalized s)
    (hne : s ≠ [])
    (hu : UniqueSuccessfulChoice s) :
    UniqueCompletePath s := by
  have main :
      ∀ n : Nat, ∀ x : RunState,
        x.length = n →
        Normalized x →
        x ≠ [] →
        UniqueSuccessfulChoice x →
        UniqueCompletePath x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro x hxlen hnx hnex hux
        rcases hux with ⟨chosen, hchosen, huniq⟩
        have hux' : UniqueSuccessfulChoice x :=
          ⟨chosen, hchosen, huniq⟩
        by_cases hone : n = 1
        · apply uniqueCompletePath_of_uniqueChoice_and_children hnex hux'
          intro ch hch
          have hlt : ch.2.length < x.length :=
            indexedStep_length_lt hch.1
          have hz : ch.2.length = 0 := by
            omega
          have hempty : ch.2 = [] :=
            List.length_eq_zero.mp hz
          rw [hempty]
          exact uniqueCompletePath_nil
        · have hpos : 0 < n := by
            cases x with
            | nil => exact (hnex rfl).elim
            | cons y ys =>
                simp at hxlen
                omega
          have hgt1 : 1 < x.length := by
            omega
          have hbridgeChoice : BridgeChoice x chosen := by
            rcases successfulChoice_classify hchosen with hnomerge | hb
            · have hchildne :=
                noMergeChoice_child_nonempty hgt1 hnomerge
              have hlift : ChildChoicesLift x chosen :=
                hno hnx hnomerge hchosen
              exact
                (uniqueChoice_forbids_full_child_exchange
                  hux' hchosen hchildne hlift).elim
            · exact hb
          rcases hbridgeChoice with
            ⟨pre, post, c, d, bp, bq, hx, hchosenEq⟩
          subst x
          subst chosen
          have hlift :
              BridgeChildChoicesLiftExceptMerged pre post c d bp bq :=
            hbridge hnx
          have hchildUnique :
              UniqueSuccessfulChoice (pre ++ (c,true) :: post) :=
            bridge_child_unique_of_exchange hchosen hux' hlift
          have hchildNorm :
              Normalized (pre ++ (c,true) :: post) :=
            indexedStep_normalized hnx hchosen.1
          have hchildNonempty :
              pre ++ (c,true) :: post ≠ [] := by
            intro he
            have hlen := congrArg List.length he
            simp at hlen
          have hchildLt :
              (pre ++ (c,true) :: post).length < n := by
            calc
              (pre ++ (c,true) :: post).length
                  < (pre ++ (c,bp) :: (d,true) :: (c,bq) :: post).length :=
                indexedStep_length_lt hchosen.1
              _ = n := hxlen
          have hchildPath :
              UniqueCompletePath (pre ++ (c,true) :: post) :=
            ih _ hchildLt
              (pre ++ (c,true) :: post) rfl
              hchildNorm hchildNonempty hchildUnique
          apply uniqueCompletePath_of_uniqueChoice_and_children
            (s := pre ++ (c,bp) :: (d,true) :: (c,bq) :: post)
            hnex hux'
          intro ch hch
          have heq :
              ch =
                (pre.length + 1, pre ++ (c,true) :: post) :=
            huniq ch hch
          subst ch
          exact hchildPath
  exact main s.length s rfl hn hne hu

/-- Conditional equivalence on normalized nonempty run states. -/
theorem uniqueSuccessfulChoice_iff_uniqueCompletePath_exchange
    (hno : NormalizedNoMergeExchange)
    (hbridge : NormalizedBridgeExchange)
    {s : RunState}
    (hn : Normalized s)
    (hne : s ≠ []) :
    UniqueSuccessfulChoice s ↔ UniqueCompletePath s := by
  constructor
  · exact uniqueCompletePath_of_uniqueSuccessfulChoice_exchange
      hno hbridge hn hne
  · exact uniqueCompletePath_uniqueSuccessfulChoice hne

end LC004
