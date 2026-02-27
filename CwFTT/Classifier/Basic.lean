import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Monadicity
import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
import Mathlib.CategoryTheory.MorphismProperty.Limits

import CwFTT.Util.Pullback
import CwFTT.Util.Cartesian
import CwFTT.Util.CartesianPullback
import CwFTT.Util.Cone


namespace CategoryTheory
open Limits
universe v u
variable {C : Type u} [Category.{v} C]

/- these lemmas should really be in Topos.Classifier or something -/
section

@[reassoc]
lemma Classifier.χ_id (𝒞 : Classifier C) (X : C) : 𝒞.χ (𝟙 X) = 𝒞.χ₀ _ ≫ 𝒞.truth :=
  (𝒞.uniq _ (χ₀' := 𝒞.χ₀ _) <| IsPullback.of_horiz_isIso_mono (by simp)).symm

@[reassoc]
lemma Classifier.comp_χ_comp (𝒞 : Classifier C) {X Y Z : C}
    (m₁ : X ⟶ Y) [Mono m₁] (m₂ : Y ⟶ Z) [Mono m₂] :
    m₂ ≫ 𝒞.χ (m₁ ≫ m₂) = 𝒞.χ m₁ := 𝒞.uniq _ (χ₀' := 𝟙 X ≫ _) <|
  .paste_vert (.of_vert_isIso_mono (by simp)) (𝒞.isPullback (m₁ ≫ m₂))

-- @[ext (iff := false)]
lemma Classifier.hom_ext (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) {Y : C} {m : Y ⟶ X}
    (χ₀ : Y ⟶ 𝒞.Ω₀) (χ₀' : Y ⟶ 𝒞.Ω₀)
    (hf : IsPullback m χ₀ f 𝒞.truth) (hg : IsPullback m χ₀' g 𝒞.truth) :
    f = g := by
  letI : Mono m := hf.mono_fst
  trans 𝒞.χ m
  · exact 𝒞.uniq _ hf
  · symm
    exact 𝒞.uniq _ hg

@[reassoc (attr := simp)]
lemma Classifier.comp_χ₀ (𝒞 : Classifier C) {X Y : C} (m : X ⟶ Y) :
  m ≫ 𝒞.χ₀ _ = 𝒞.χ₀ _ := Subsingleton.elim _ _

-- @[simp high] -- guaranteed solve.
lemma Classifier.eq_χ₀ (𝒞 : Classifier C) {X : C} (m : X ⟶ 𝒞.Ω₀) :
  m = 𝒞.χ₀ X := Subsingleton.elim _ _

@[simp]
lemma Classifier.χ₀_Ω₀ (𝒞 : Classifier C) : 𝒞.χ₀ 𝒞.Ω₀ = 𝟙 _ :=
  Subsingleton.elim _ _

@[simp]
lemma Classifier.χ_pullback_fst (𝒞 : Classifier C) {X : C} (a : X ⟶ 𝒞.Ω) [HasPullback a 𝒞.truth] :
  𝒞.χ (pullback.fst a 𝒞.truth) = a := by
  symm
  apply 𝒞.uniq
  exact .of_hasPullback _ _

@[simp]
lemma Classifier.χ_truth (𝒞 : Classifier C) : 𝒞.χ 𝒞.truth = 𝟙 𝒞.Ω := by
  symm
  apply 𝒞.uniq
  exact .id_vert 𝒞.truth

lemma Classifier.eq_χ_iff_comp_factors_truth_iff (𝒞 : Classifier C) {X Y : C} (f : Y ⟶ 𝒞.Ω)
    (g : X ⟶ Y) [Mono g] : f = 𝒞.χ g ↔
    ∀ {Z : C} (j : Z ⟶ Y), (j ≫ f = 𝒞.χ₀ _ ≫ 𝒞.truth ↔ j ≫ 𝒞.χ g = 𝒞.χ₀ _ ≫ 𝒞.truth) := by
  constructor
  · rintro rfl
    simp
  · intro h
    apply 𝒞.uniq _ (χ₀' := 𝒞.χ₀ _)
    refine {
      w := (h g).mpr (𝒞.isPullback _ ).w
      isLimit' := ⟨by
        refine PullbackCone.IsLimit.mk _
          (fun s => (𝒞.isPullback g).lift s.fst s.snd (by
            rw [Subsingleton.elim s.snd (𝒞.χ₀ _), ← h,s.condition, Subsingleton.elim s.snd]))
          (by
            intro s
            rw [IsPullback.lift_fst])
          (by
            intro s
            rw [IsPullback.lift_snd])
          (by
            intro s m hm₁ hm₂
            dsimp
            generalize_proofs hpb h
            apply hpb.hom_ext <;> simp_all)
        ⟩
    }

end
end CategoryTheory
