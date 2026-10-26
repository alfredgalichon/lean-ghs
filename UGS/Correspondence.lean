import Mathlib.Order.Lattice
import Mathlib.Tactic.Push

/-!
# Inverse isotonicity for correspondences (Theorem 22)

Theorem 22 of the unified-gross-substitutes self-lecture — GSV Theorem 1 — for a
supply *correspondence* `Q : (ι → α) → (ι → α) → Prop`, `Q p q` reading
"the quantity `q` is attainable at the price `p`". Prices and quantities are
vectors in `ι → α` with `α` a linear order; `⊓`/`⊔` are the coordinatewise
meet/join.

Definitions follow Galichon–Samuelson–Vernet (Def. 1, 2, 8), **supply
convention**. In particular unified gross substitutes says the meet witness
`qm ∈ Q(p ⊓ p')` is bounded *below* and the join witness `qj ∈ Q(p ⊔ p')` bounded
*above*, coordinate by coordinate — this is the orientation that makes the
theorem work (the self-lecture's `def:UGS` had these two inequalities flipped,
which is why its forward-direction proof could not close).

* `isUGS_nonreversing_iff_totallyIsotoneInverse` : for a UGS correspondence,
  `Nonreversing` ↔ `TotallyIsotoneInverse` (GSV Theorem 1, with GSV's
  `B`-parametrized Definition 8). Both directions are proved. The forward
  direction is GSV's argument: UGS produces a meet witness `qm ≥ q` (using
  `q ≤ q'` on the coordinates outside `B`), which — at the lower price `p ⊓ p'`
  — is a *reversal* against `q` at the higher price `p`, so nonreversingness
  places `q` in `Q(p ⊓ p')`; dually for the join.
-/

namespace Correspondence

variable {ι : Type*} {α : Type*} [LinearOrder α]

/-- **Unified gross substitutes** (GSV Definition 1, supply convention). For
`q ∈ Q(p)` and `q' ∈ Q(p')` there are a meet witness `qm ∈ Q(p ⊓ p')` bounded
below and a join witness `qj ∈ Q(p ⊔ p')` bounded above, coordinate by
coordinate according to the sign of `p_z - p'_z`. -/
def IsUGS (Q : (ι → α) → (ι → α) → Prop) : Prop :=
  ∀ p p' q q', Q p q → Q p' q' →
    ∃ qm qj, Q (p ⊓ p') qm ∧ Q (p ⊔ p') qj ∧
      ∀ z, (p z ≤ p' z → q z ≤ qm z ∧ qj z ≤ q' z) ∧
           (p' z < p z → q' z ≤ qm z ∧ qj z ≤ q z)

/-- `Q` is **nonreversing** (GSV Definition 2): if the higher price `p'` carries
the lower quantity `q'` (`p ≤ p'`, `q' ≤ q`), each quantity is attainable at each
price. -/
def Nonreversing (Q : (ι → α) → (ι → α) → Prop) : Prop :=
  ∀ p p' q q', Q p q → Q p' q' → p ≤ p' → q' ≤ q → Q p' q ∧ Q p q'

/-- `Q` has **totally isotone inverse** (GSV Definition 8) — the strong,
`B`-parametrized form of `Q⁻¹` being isotone in the strong (Veinott) set order.
Whenever `q ∈ Q(p)` and `q' ∈ Q(p')` admit a coordinate predicate `B` with
`p z ≤ p' z` for `z ∈ B` and `q z ≤ q' z` for `z ∉ B`, the meet price carries `q`
and the join price carries `q'`. Taking `B = ∅` recovers plain inverse
isotonicity; a general `B` is strictly stronger. -/
def TotallyIsotoneInverse (Q : (ι → α) → (ι → α) → Prop) : Prop :=
  ∀ p p' q q' (B : ι → Prop), Q p q → Q p' q' →
    (∀ z, B z → p z ≤ p' z) → (∀ z, ¬ B z → q z ≤ q' z) →
    Q (p ⊓ p') q ∧ Q (p ⊔ p') q'

/-- **Theorem 22** (GSV Theorem 1). A correspondence satisfying unified gross
substitutes is nonreversing if and only if it has totally isotone inverse. -/
theorem isUGS_nonreversing_iff_totallyIsotoneInverse
    {Q : (ι → α) → (ι → α) → Prop} (hUGS : IsUGS Q) :
    Nonreversing Q ↔ TotallyIsotoneInverse Q := by
  constructor
  · -- (⇒) UGS + nonreversing gives totally isotone inverse.
    intro hNR p p' q q' B hq hq' hB1 hB2
    obtain ⟨qm, qj, hqm, hqj, hb⟩ := hUGS p p' q q' hq hq'
    -- The meet witness dominates `q`, the join witness is dominated by `q'`;
    -- on coordinates with `p z > p' z` we have `z ∉ B`, so `q z ≤ q' z`.
    have hqm' : q ≤ qm := by
      intro z
      by_cases hz : p z ≤ p' z
      · exact ((hb z).1 hz).1
      · push_neg at hz
        have hnB : ¬ B z := fun hbz => absurd (hB1 z hbz) (not_le.mpr hz)
        exact le_trans (hB2 z hnB) ((hb z).2 hz).1
    have hqj' : qj ≤ q' := by
      intro z
      by_cases hz : p z ≤ p' z
      · exact ((hb z).1 hz).2
      · push_neg at hz
        have hnB : ¬ B z := fun hbz => absurd (hB1 z hbz) (not_le.mpr hz)
        exact le_trans ((hb z).2 hz).2 (hB2 z hnB)
    exact ⟨(hNR (p ⊓ p') p qm q hqm hq inf_le_left hqm').2,
           (hNR p' (p ⊔ p') q' qj hq' hqj le_sup_right hqj').1⟩
  · -- (⇐) totally isotone inverse (already at `B = ∅`) gives nonreversing:
    -- for `p ≤ p'`, `p' ⊓ p = p` and `p' ⊔ p = p'`.
    intro hTII p p' q q' hq hq' hpp' hq'q
    have h := hTII p' p q' q (fun _ => False) hq' hq (fun _ hb => hb.elim) (fun z _ => hq'q z)
    rw [inf_eq_right.mpr hpp', sup_eq_left.mpr hpp'] at h
    exact ⟨h.2, h.1⟩

/-! ## Corollary 1 and Theorem 2 -/

/-- **Corollary 1** (GSV). For a UGS nonreversing correspondence each fibre
`Q⁻¹(q) = {p | Q p q}` is a sublattice: if `p` and `p'` both support `q`, so do
`p ⊓ p'` and `p ⊔ p'`. Immediate from Theorem 1 at `B = ∅`, `q' = q`. -/
theorem fibre_sublattice {Q : (ι → α) → (ι → α) → Prop} (hUGS : IsUGS Q)
    (hNR : Nonreversing Q) {q p p' : ι → α} (hp : Q p q) (hp' : Q p' q) :
    Q (p ⊓ p') q ∧ Q (p ⊔ p') q :=
  (isUGS_nonreversing_iff_totallyIsotoneInverse hUGS).mp hNR
    p p' q q (fun _ => False) hp hp' (fun _ hb => hb.elim) (fun z _ => le_refl (q z))

/-- `Q` is **strongly nonreversing** (GSV Definition 3): `q ∈ Q(p)`, `q' ∈ Q(p')`,
`p ≤ p'` and `q' ≤ q` force `p = p'`. -/
def StronglyNonreversing (Q : (ι → α) → (ι → α) → Prop) : Prop :=
  ∀ p p' q q', Q p q → Q p' q' → p ≤ p' → q' ≤ q → p = p'

/-- An **M-correspondence** (GSV Definition 7): a UGS correspondence that is
strongly nonreversing. -/
def IsMCorr (Q : (ι → α) → (ι → α) → Prop) : Prop :=
  IsUGS Q ∧ StronglyNonreversing Q

/-- `Q⁻¹` is **point-valued and isotone where nonempty** (Theorem 2(ii)):
`q ∈ Q(p)`, `q' ∈ Q(p')` and `q ≤ q'` force `p ≤ p'`. -/
def PointValuedIsotoneInverse (Q : (ι → α) → (ι → α) → Prop) : Prop :=
  ∀ p p' q q', Q p q → Q p' q' → q ≤ q' → p ≤ p'

/-- Strong nonreversingness implies (weak) nonreversingness: the reversal forces
`p = p'`, and then both quantities already sit at that single price. -/
theorem StronglyNonreversing.nonreversing {Q : (ι → α) → (ι → α) → Prop}
    (hS : StronglyNonreversing Q) : Nonreversing Q := by
  intro p p' q q' hq hq' hpp' hq'q
  have hpe : p = p' := hS p p' q q' hq hq' hpp' hq'q
  subst hpe
  exact ⟨hq, hq'⟩

/-- **Theorem 2**, (i)⟺(iii): under UGS, being an M-correspondence coincides with
being strongly nonreversing. -/
theorem isMCorr_iff_stronglyNonreversing {Q : (ι → α) → (ι → α) → Prop}
    (hUGS : IsUGS Q) : IsMCorr Q ↔ StronglyNonreversing Q :=
  ⟨fun h => h.2, fun h => ⟨hUGS, h⟩⟩

/-- **Theorem 2**, (ii)⟺(iii): under UGS, `Q⁻¹` is point-valued and isotone iff
`Q` is strongly nonreversing. Together with the previous lemma this is GSV's
three-way equivalence. -/
theorem pointValuedIsotoneInverse_iff_stronglyNonreversing
    {Q : (ι → α) → (ι → α) → Prop} (hUGS : IsUGS Q) :
    PointValuedIsotoneInverse Q ↔ StronglyNonreversing Q := by
  constructor
  · -- (ii) ⟹ (iii): isotonicity both ways pins `p = p'`. (No UGS needed.)
    intro hII p p' q q' hq hq' hpp' hq'q
    exact le_antisymm hpp' (hII p' p q' q hq' hq hq'q)
  · -- (iii) ⟹ (ii): Theorem 1 sends `q` into `Q(p ⊓ p')`; strong nonreversing
    -- against `q ∈ Q(p)` collapses `p ⊓ p' = p`, i.e. `p ≤ p'`.
    intro hSNR p p' q q' hq hq' hqq'
    have hTII := (isUGS_nonreversing_iff_totallyIsotoneInverse hUGS).mp hSNR.nonreversing
    have h := hTII p p' q q' (fun _ => False) hq hq' (fun _ hb => hb.elim) (fun z _ => hqq' z)
    have hpe : p ⊓ p' = p := hSNR (p ⊓ p') p q q h.1 hq inf_le_left (le_refl q)
    calc p = p ⊓ p' := hpe.symm
      _ ≤ p' := inf_le_right

/-! ## Sufficient conditions for nonreversingness (Properties 5–16) -/

/-- If the reversal antecedent (`p ≤ p'` yet `q' ≤ q`) can only occur with
`q = q'`, then `Q` is nonreversing. This is the common mechanism behind the
aggregate-output sufficient conditions (Properties 5–7). -/
theorem nonreversing_of_forces_eq {Q : (ι → α) → (ι → α) → Prop}
    (h : ∀ p p' q q', Q p q → Q p' q' → p ≤ p' → q' ≤ q → q = q') :
    Nonreversing Q := by
  intro p p' q q' hq hq' hpp' hq'q
  have hqe : q = q' := h p p' q q' hq hq' hpp' hq'q
  subst hqe
  exact ⟨hq', hq⟩

/-- `Q` is a **P-correspondence** (GSV Property 12): `q ∈ Q(p)`, `q' ∈ Q(p')`,
`q' ≤ q` and `p ≤ p'` force `p = p'`. This is exactly strong nonreversingness. -/
def IsPCorrespondence (Q : (ι → α) → (ι → α) → Prop) : Prop :=
  ∀ p p' q q', Q p q → Q p' q' → q' ≤ q → p ≤ p' → p = p'

/-- **Property 12.** A P-correspondence is nonreversing. -/
theorem IsPCorrespondence.nonreversing {Q : (ι → α) → (ι → α) → Prop}
    (hP : IsPCorrespondence Q) : Nonreversing Q := by
  apply StronglyNonreversing.nonreversing
  intro p p' q q' hq hq' hpp' hq'q
  exact hP p p' q q' hq hq' hq'q hpp'

/-- `Q` has the **Kelso–Crawford substitutes** property (GSV §3.1): whenever
`p' ≤ p` and `q ∈ Q(p)`, some `q' ∈ Q(p')` has `q z ≤ q' z` on the coordinates
where the price is unchanged (`p z = p' z`). -/
def KCsubstitutes (Q : (ι → α) → (ι → α) → Prop) : Prop :=
  ∀ p p', p' ≤ p → ∀ q, Q p q → ∃ q', Q p' q' ∧ ∀ z, p z = p' z → q z ≤ q' z

/-- **Property 16.** Unified gross substitutes implies Kelso–Crawford substitutes,
given a nonempty upper fibre (a witness `q'' ∈ Q(p')`): the UGS meet witness at
`p ⊓ p' = p'` is the required allocation, and on unchanged coordinates the case
`p z ≤ p' z` of `IsUGS` gives `q z ≤ qm z`. -/
theorem isUGS_kc {Q : (ι → α) → (ι → α) → Prop} (hUGS : IsUGS Q)
    {p p' : ι → α} (hpp' : p' ≤ p) {q : ι → α} (hq : Q p q)
    {q'' : ι → α} (hq'' : Q p' q'') :
    ∃ q', Q p' q' ∧ ∀ z, p z = p' z → q z ≤ q' z := by
  obtain ⟨qm, _qj, hqm, _hqj, hb⟩ := hUGS p p' q q'' hq hq''
  rw [inf_eq_right.mpr hpp'] at hqm
  exact ⟨qm, hqm, fun z hz => ((hb z).1 (le_of_eq hz)).1⟩

/-- **Property 16, quantified form.** A UGS correspondence with nonempty
fibres satisfies the Kelso--Crawford substitutes property.  The nonemptiness
hypothesis supplies the comparison allocation required by the binary UGS
axiom. -/
theorem IsUGS.kc {Q : (ι → α) → (ι → α) → Prop} (hUGS : IsUGS Q)
    (hne : ∀ p, ∃ q, Q p q) : KCsubstitutes Q := by
  intro p p' hpp' q hq
  obtain ⟨q'', hq''⟩ := hne p'
  exact isUGS_kc hUGS hpp' hq hq''

/-- The **other Kelso--Crawford clause**: whenever `p' ≤ p` and `q' ∈ Q(p')`, some
`q ∈ Q(p)` has `q z ≤ q' z` on the coordinates where the price is unchanged.
Kelso and Crawford impose only one of the two clauses; the lecture's Property on
unified gross substitutes asserts both, and `IsUGS.kcA` below is the certificate
for this one. -/
def KCsubstitutesA (Q : (ι → α) → (ι → α) → Prop) : Prop :=
  ∀ p p', p' ≤ p → ∀ q', Q p' q' → ∃ q, Q p q ∧ ∀ z, p z = p' z → q z ≤ q' z

/-- Unified gross substitutes implies the second Kelso--Crawford clause, given a
nonempty lower fibre. Same application of `IsUGS` as `isUGS_kc`, read off the
*join* witness instead of the meet: at `p ⊔ p' = p` the case `p z ≤ p' z` of
`IsUGS` gives `qj z ≤ q' z` on the unchanged coordinates. -/
theorem isUGS_kcA {Q : (ι → α) → (ι → α) → Prop} (hUGS : IsUGS Q)
    {p p' : ι → α} (hpp' : p' ≤ p) {q' : ι → α} (hq' : Q p' q')
    {q'' : ι → α} (hq'' : Q p q'') :
    ∃ q, Q p q ∧ ∀ z, p z = p' z → q z ≤ q' z := by
  obtain ⟨_qm, qj, _hqm, hqj, hb⟩ := hUGS p p' q'' q' hq'' hq'
  rw [sup_eq_left.mpr hpp'] at hqj
  exact ⟨qj, hqj, fun z hz => ((hb z).1 (le_of_eq hz)).2⟩

/-- Quantified form: a UGS correspondence with nonempty fibres satisfies the
second Kelso--Crawford clause too, so it satisfies the full two-clause property
of the lecture. -/
theorem IsUGS.kcA {Q : (ι → α) → (ι → α) → Prop} (hUGS : IsUGS Q)
    (hne : ∀ p, ∃ q, Q p q) : KCsubstitutesA Q := by
  intro p p' hpp' q' hq'
  obtain ⟨q'', hq''⟩ := hne p
  exact isUGS_kcA hUGS hpp' hq' hq''

variable {β : Type*} [PartialOrder β]

/-- **Single crossing** of an objective `φ` (GSV Property 11): for `p ≤ p'` and
`q' ≤ q`, if `φ p' q ≤ φ p' q'` and `φ p q' ≤ φ p q`, then both are equalities. -/
def SingleCrossing (φ : (ι → α) → (ι → α) → β) : Prop :=
  ∀ p p' q q', p ≤ p' → q' ≤ q → φ p' q ≤ φ p' q' → φ p q' ≤ φ p q →
    φ p' q = φ p' q' ∧ φ p q = φ p q'

/-- The **argmax correspondence** of `φ` over a constraint set `S` (a predicate on
quantities): `q ∈ Q(p)` iff `q ∈ S` and `q` maximizes `φ p ·` over `S`. -/
def argmaxCorrOn (φ : (ι → α) → (ι → α) → β) (S : (ι → α) → Prop) :
    (ι → α) → (ι → α) → Prop :=
  fun p q => S q ∧ ∀ r, S r → φ p r ≤ φ p q

/-- **Property 11** (both directions). `φ` has single crossing if and only if its
constrained argmax correspondence is nonreversing for every constraint set `S`.
The converse takes the two-point set `S = {q, q'}`. -/
theorem singleCrossing_iff_forall_argmaxOn_nonreversing
    {φ : (ι → α) → (ι → α) → β} :
    SingleCrossing φ ↔ ∀ S, Nonreversing (argmaxCorrOn φ S) := by
  constructor
  · -- single crossing ⟹ every constrained argmax is nonreversing
    intro hSC S p p' q q' hq hq' hpp' hq'q
    obtain ⟨hqS, hqmax⟩ := hq
    obtain ⟨hq'S, hq'max⟩ := hq'
    obtain ⟨e1, e2⟩ := hSC p p' q q' hpp' hq'q (hq'max q hqS) (hqmax q' hq'S)
    refine ⟨⟨hqS, fun r hr => ?_⟩, ⟨hq'S, fun r hr => ?_⟩⟩
    · rw [e1]; exact hq'max r hr
    · rw [← e2]; exact hqmax r hr
  · -- nonreversing on every constraint set ⟹ single crossing (use `S = {q, q'}`)
    intro hNR p p' q q' hpp' hq'q hφ1 hφ2
    have hqmem : argmaxCorrOn φ (fun r => r = q ∨ r = q') p q :=
      ⟨Or.inl rfl, fun r hr => by rcases hr with rfl | rfl; exacts [le_refl _, hφ2]⟩
    have hq'mem : argmaxCorrOn φ (fun r => r = q ∨ r = q') p' q' :=
      ⟨Or.inr rfl, fun r hr => by rcases hr with rfl | rfl; exacts [hφ1, le_refl _]⟩
    obtain ⟨hq_p', hq'_p⟩ :=
      hNR (fun r => r = q ∨ r = q') p p' q q' hqmem hq'mem hpp' hq'q
    exact ⟨le_antisymm hφ1 (hq_p'.2 q' (Or.inr rfl)),
           le_antisymm (hq'_p.2 q (Or.inl rfl)) hφ2⟩
