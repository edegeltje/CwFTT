import CwFTT.Util.Pullback
import CwFTT.Util.Cartesian
import CwFTT.Util.CartesianPullback
import CwFTT.Util.Cone
import CwFTT.Classifier.Colimit
import CwFTT.Classifier.Ops.And
import CwFTT.Classifier.Ops.Eq



namespace CategoryTheory.Classifier
open Limits
universe v u
variable {C : Type u} [Category.{v} C]

open MonoidalCategory CartesianMonoidalCategory

/-- `(X → Y)` iff `(X ∧ Y) = X` -/
def imp (𝒞 : Classifier C) [CartesianMonoidalCategory C] :
  𝒞.Ω ⊗ 𝒞.Ω ⟶ 𝒞.Ω := lift (fst _ _) (𝒞.and) ≫ (𝒞.eq 𝒞.Ω)

lemma impl_isPullback (𝒞 : Classifier C) [HasEqualizers C]
    [CartesianMonoidalCategory C] : IsPullback (equalizer.ι (fst _ _) (𝒞.and))
    (𝒞.χ₀ _) 𝒞.imp 𝒞.truth := by
  unfold imp
  rw [← 𝒞.comp_χ₀ (equalizer.ι (fst _ _) 𝒞.and ≫ fst _ _)]
  exact IsPullback.paste_vert (.equalizer_monoidal _ _) (𝒞.eq_isPullback _)

/-
(∧ implies left) is true
(∧ implies right) is true
(⊥ implies _) is true
(_ implies ⊤) is true
(left implies ∨) is true
(right implies ∨) is true


-/

/-
(a ∧ b) ≤ c ↔ a ≤ (b → c)
(a → b) = true ↔ a ≤ b
-/

/-- `impl` internalizes implication. -/
lemma imp_eq_truth_iff_le (𝒞 : Classifier C)
    [CartesianMonoidalCategory C] {X : C} (f g : X ⟶ 𝒞.Ω) :
    lift f g ≫ 𝒞.imp = 𝒞.χ₀ _ ≫ 𝒞.truth ↔
    f ≤ g := by
  constructor
  · intro h
    dsimp [imp] at h
    rw [comp_lift_assoc, lift_fst, 𝒞.eq_eq_truth_iff] at h
    exact h.symm
  · intro h
    dsimp [imp]
    rw [comp_lift_assoc,lift_fst,h,𝒞.eq_eq_truth_iff]

section himp
variable [CartesianMonoidalCategory C]
open CartesianMonoidalCategory

instance (𝒞 : Classifier C) (X : C) : HImp (X ⟶ 𝒞.Ω) where
  himp f g := lift f g ≫ 𝒞.imp

lemma himp_def (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) :
  f ⇨ g = lift f g ≫ 𝒞.imp := rfl

attribute [local instance] CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory in
lemma propext (𝒞 : Classifier C) :
    𝒞.eq 𝒞.Ω = lift (𝒞.imp) ((β_ _ _).hom ≫ 𝒞.imp) ≫ 𝒞.and := by
  symm
  dsimp [eq]
  rw [𝒞.eq_χ_iff_comp_factors_truth_iff]
  rw [← eq.eq_1]
  intro Z j
  rw [comp_lift_assoc,𝒞.and_eq_truth_iff]
  nth_rw 2 3[← lift_comp_fst_snd j]
  rw [← comp_lift_assoc, lift_braiding_hom_assoc, eq_eq_truth_iff,
    ← lift_comp_fst_snd j, imp_eq_truth_iff_le, le_def, comp_lift_assoc, imp_eq_truth_iff_le,
      lift_snd,lift_fst,lift_comp_fst_snd,le_def,and_comm,lift_comp_fst_snd]
  constructor
  · intro ⟨h1, h2⟩
    rw [← h1,← h2]
  · intro h
    nth_rw 1 3 [← lift_comp_fst_snd j]
    rw [← h, and_refl]
    simp

lemma himp_counit [HasPullbacks C] (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) :
    (f ⊓ (f ⇨ g)) ≤ g := by
  rw [𝒞.le_def]
  rw [← 𝒞.χ_pullback_fst (f ⊓ (f ⇨ g)),
    𝒞.eq_χ_iff_comp_factors_truth_iff, 𝒞.χ_pullback_fst]
  intro Z j
  rw [comp_lift_assoc,and_eq_truth_iff, 𝒞.inf_def,comp_lift_assoc,
    and_eq_truth_iff,𝒞.himp_def,comp_lift_assoc,imp_eq_truth_iff_le, le_def]
  simp_all

lemma himp_unit [HasPullbacks C] (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) :
    g ≤ f ⇨ (f ⊓ g) := by
  rw [𝒞.le_def]
  rw [← 𝒞.χ_pullback_fst g, 𝒞.eq_χ_iff_comp_factors_truth_iff, 𝒞.χ_pullback_fst]
  intro Z j
  rw [comp_lift_assoc, and_eq_truth_iff, himp_def,comp_lift_assoc,
    imp_eq_truth_iff_le, inf_def, comp_lift_assoc]
  simp_all

lemma himp_monotone [HasPullbacks C] (𝒞 : Classifier C) {X : C} (f : X ⟶ 𝒞.Ω) ⦃g h : X ⟶ 𝒞.Ω⦄ :
    g ≤ h → f ⇨ g ≤ f ⇨ h := by
  intro hle
  rw [le_def]
  rw [← 𝒞.χ_pullback_fst (f ⇨ g), 𝒞.eq_χ_iff_comp_factors_truth_iff,
    𝒞.χ_pullback_fst]
  intro Z j
  simp_rw [comp_lift_assoc, and_eq_truth_iff, himp_def, comp_lift_assoc,
    imp_eq_truth_iff_le, and_iff_left_iff_imp]
  intro hle'
  exact le_trans hle' (precomp_monotone 𝒞 j hle)

lemma le_himp_iff [HasPullbacks C] (𝒞 : Classifier C) {X : C} (f g h : X ⟶ 𝒞.Ω) :
    f ≤ (g ⇨ h) ↔ f ⊓ g ≤ h := by
  constructor
  · intro hle
    apply le_trans _ (𝒞.himp_counit g h)
    rw [inf_comm]
    apply inf_le_inf_left _ hle
  · intro hle
    apply le_trans (𝒞.himp_unit g f)
    rw [inf_comm]
    apply himp_monotone _ _ hle

lemma himp_antitone [HasPullbacks C] (𝒞 : Classifier C) {X : C} (f g h : X ⟶ 𝒞.Ω) :
    f ≤ g → (g ⇨ h ≤ f ⇨ h) := by
  intro hle
  rw [le_himp_iff,inf_comm]
  apply le_trans _ (himp_counit _ g _)
  exact inf_le_inf_right _ hle

lemma himp_himp_eq_and_himp [HasPullbacks C] (𝒞 : Classifier C) {X : C} (f g h : X ⟶ 𝒞.Ω) :
    f ⇨ (g ⇨ h) = (f ⊓ g) ⇨ h := by
  apply le_antisymm
  · rw [le_himp_iff,← inf_assoc,inf_comm _ f]
    trans ((g ⇨ h) ⊓ g)
    · apply inf_le_inf_right
      exact himp_counit _ _ _
    · rw [inf_comm]
      exact himp_counit _ _ _
  · rw [le_himp_iff,le_himp_iff, inf_assoc, inf_comm]
    exact himp_counit 𝒞 (f ⊓ g) h

lemma le_himp_himp [HasPullbacks C] (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) :
    f ≤ ((f ⇨ g) ⇨ g) := by
  rw [le_himp_iff]
  exact himp_counit _ _ _

lemma top_himp_himp_eq [HasPullbacks C] (𝒞 : Classifier C) {X : C} (g : X ⟶ 𝒞.Ω) :
  ((⊤ ⇨ g) ⇨ g) = ⊤ := by
  rw [eq_top_iff]
  exact le_himp_himp _ _ _

lemma himp_himp_himp_le_himp [HasPullbacks C] (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) :
    (((f ⇨ g) ⇨ g) ⇨ g) = (f ⇨ g) := by
  apply le_antisymm
  · rw [le_himp_iff]
    trans (((f ⇨ g) ⇨ g) ⇨ g) ⊓ ((f ⇨ g) ⇨ g)
    · apply inf_le_inf_left
      exact (le_himp_himp _ f g)
    · rw [inf_comm]
      exact himp_counit _ _ _
  · exact le_himp_himp _ _ _

lemma inf_himp_himp_eq_himp_himp_and_himp_himp [HasPullbacks C] (𝒞 : Classifier C) {X : C}
    (f g h : X ⟶ 𝒞.Ω) : ((f ⊓ g) ⇨ h) ⇨ h = ((f ⇨ h) ⇨ h) ⊓ ((g ⇨ h) ⇨ h) := by
  apply le_antisymm
  · apply le_inf
    · rw [le_himp_iff,inf_comm]
      apply le_trans _ (himp_counit _ ((f ⊓ g) ⇨ h) _)
      apply inf_le_inf_right
      rw [le_himp_iff]
      apply le_trans _ (himp_counit _ f _)
      rw [inf_comm]
      exact inf_le_inf_right _ (inf_le_left)
    · rw [le_himp_iff,inf_comm]
      apply le_trans _ (himp_counit _ ((f ⊓ g) ⇨ h) _)
      apply inf_le_inf_right
      rw [le_himp_iff,inf_comm]
      apply le_trans _ (himp_counit _ g _)
      exact inf_le_inf_right _ (inf_le_right)
  · rw [le_himp_iff,inf_assoc,inf_comm]
    apply le_trans _ (himp_counit _ (f ⇨ h) _)
    apply inf_le_inf_right
    rw [le_himp_iff,inf_assoc,inf_comm]
    apply le_trans _ (himp_counit _ (g ⇨ h) _)
    apply inf_le_inf_right
    rw [le_himp_iff,inf_assoc,inf_comm]
    exact himp_counit _ _ _



end himp

end CategoryTheory.Classifier
