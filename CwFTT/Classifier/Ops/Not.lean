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
import CwFTT.Classifier.Colimit
import CwFTT.Classifier.Ops.Impl


namespace CategoryTheory
open Limits
universe v u
variable {C : Type u} [Category.{v} C]


noncomputable def Classifier.not (𝒞 : Classifier C) [HasFiniteLimits C] [HasClassifier C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] : 𝒞.Ω ⟶ 𝒞.Ω := 𝒞.χ (
  equalizer.ι (𝟙 _) (𝒞.χ₀ _ ≫ 𝒞.falsity))


@[reassoc (attr := simp)]
lemma Classifier.truth_not (𝒞 : Classifier C) [HasFiniteLimits C] [HasClassifier C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] :
    𝒞.truth ≫ 𝒞.not = 𝒞.falsity := by
  unfold falsity
  apply 𝒞.uniq (initial.to _)
  apply IsPullback.paste_vert _ (𝒞.isPullback _)
  sorry

@[reassoc (attr := simp)]
lemma Classifier.falsity_not (𝒞 : Classifier C) [HasFiniteLimits C] [HasClassifier C]
    [CartesianMonoidalCategory C] [MonoidalClosed C] :
    𝒞.falsity ≫ 𝒞.not = 𝒞.truth := by
  apply 𝒞.hom_ext _ _ (m := 𝟙 𝒞.Ω₀) (𝒞.χ₀ _) (𝟙 _)
  · unfold not
    rw [← 𝒞.comp_χ₀ (equalizer.lift (f := 𝟙 𝒞.Ω) (g := 𝒞.χ₀ _ ≫ 𝒞.falsity) (𝒞.falsity) (by simp))]
    apply IsPullback.paste_vert _ (𝒞.isPullback _)
    -- basically, the square commutes and one corner is initial
    refine {
      w := by simp
      isLimit' := by
        constructor
        have := 𝒞.isTerminalΩ₀
        exact PullbackCone.IsLimit.mk _ (fun _ => 𝒞.χ₀ _) (by cat_disch)
          (by
            intro s
            simp only
            rw [← 𝒞.comp_χ₀ s.fst]
            apply equalizer.hom_ext
            simp [s.condition])
          (by
            intro s m hm₁ hm₂
            simp_all [Subsingleton.elim s.fst (𝒞.χ₀ _)])
    }
  · exact IsKernelPair.id_of_mono 𝒞.truth

-- /-- not not Truth is the same as Truth.
-- NOTE: this is not the same as saying that P is the same as not not P!  -/
-- lemma Classifier.truth_not_not (𝒞 : Classifier C) [HasFiniteLimits C] [HasClassifier C]
--     [CartesianMonoidalCategory C] [MonoidalClosed C] :
--     𝒞.truth ≫ 𝒞.not ≫ 𝒞.not = 𝒞.truth := by
--   rw [𝒞.truth_not_assoc,𝒞.falsity_not]



-- lemma Classifier.not_not_not
-- lemma Classifier.not_truth
-- lemma Classifier.not_false
-- somehow, express what taking the pullback of `χ ≫ not` is like
