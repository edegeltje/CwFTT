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
import CwFTT.Classifier.Ops.And


namespace CategoryTheory
open Limits
universe v u
variable {C : Type u} [Category.{v} C]

open MonoidalCategory CartesianMonoidalCategory

section impl

-- noncomputable def Classifier.impl (𝒞 : Classifier C) [HasFiniteLimits C]
--     [CartesianMonoidalCategory C] :
--   𝒞.Ω ⊗ 𝒞.Ω ⟶ 𝒞.Ω := 𝒞.χ (equalizer.ι (fst _ _) (𝒞.and))

def Classifier.impl' (𝒞 : Classifier C) [CartesianMonoidalCategory C] :
  𝒞.Ω ⊗ 𝒞.Ω ⟶ 𝒞.Ω := lift (fst _ _) (𝒞.and) ≫ (𝒞.χ (lift (𝟙 _) (𝟙 _)))

-- lemma Classifier.impl_isPullback

/-
(∧ implies left) is true
(∧ implies right) is true
(⊥ implies _) is true
(_ implies ⊤) is true
(left implies ∨) is true
(right implies ∨) is true


-/

-- lemma Classifier.impl_and (𝒞 : Classifier C) [HasFiniteLimits C]
--     [CartesianMonoidalCategory C]
--     {X Y : C} (f g : X ⟶ 𝒞.Ω) : lift (lift f g ≫ 𝒞.and) f ≫ 𝒞.impl = 𝒞.χ (𝟙 _) := by
--   apply 𝒞.uniq
--   · unfold impl
--     apply IsPullback.paste_vert _ (𝒞.isPullback _)
--     · exact equalizer.lift (lift (lift f g ≫ 𝒞.and) g) (by
--         simp [𝒞.and_assoc,← 𝒞.χ_pullback_fst g, 𝒞.and_refl'])
--     ·
--       sorry

end impl

section not
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

end not

section image
variable [HasFiniteLimits C] [HasClassifier C] [CartesianMonoidalCategory C]
  [MonoidalClosed C]

noncomputable def Topos.imageFactorization {X Y : C} (f : X ⟶ Y) : ImageFactorisation f where
  F.I := equalizer (pushout.inl f f) (pushout.inr f f)
  F.m := equalizer.ι _ _
  F.m_mono := equalizer.ι_mono
  F.e := equalizer.lift f (pushout.condition)
  F.fac := equalizer.lift_ι _ _
  isImage.lift z := by
      have : RegularMono z.m := regularMonoOfMono z.m
      apply Fork.IsLimit.lift (this.isLimit) (equalizer.ι _ _)
      have := congr(z.e ≫ $(this.w))
      simp_rw [reassoc_of% z.fac] at this
      rw [← pushout.inl_desc _ _ this,equalizer.condition_assoc,pushout.inr_desc]
  isImage.lift_fac z := by
      apply Fork.IsLimit.lift_ι


instance {X Y : C} (f : X ⟶ Y) : HasImage f where
  exists_image := ⟨Topos.imageFactorization f⟩

instance : HasImages C where
  has_image _ := inferInstance

/-
TODO :
Show that coequalizers are preserved under pullback
For this, it suffices to show that Topoi are LCC
For this, we need to show that the Over-categories are CC
For this, we need to show that Topoi have *partial map* classifiers

-/

-- instance : IsRegularEpiCategory C where
--   regularEpiOfEpi {X Y} f _ := ⟨{
--     W := (pullback f f)
--     left := (pullback.fst f f)
--     right := (pullback.snd f f)
--     w := (pullback.condition)
--     isColimit := (by
--       sorry)
--   }⟩

-- example {X Y : C} (f : X ⟶ Y) : Epi (factorThruImage f) := inferInstance

-- instance : HasImageMaps C where
--   has_image_map {f g} x := {
--     has_image_map := ⟨{
--       map := _
--       map_ι := _
--     }⟩
--   }

end image

section or
open MonoidalCategory

-- variable [HasFiniteLimits C] [HasClassifier C] [CartesianMonoidalCategory C]
--   [MonoidalClosed C] in
-- #synth HasImages C

noncomputable def Classifier.or_aux
    [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] (𝒞 : Classifier C) :
    letI : HasClassifier C := ⟨⟨𝒞⟩⟩
    pushout 𝒞.truth 𝒞.truth ⟶ (𝒞.Ω ⊗ 𝒞.Ω) :=
  letI : HasClassifier C := ⟨⟨𝒞⟩⟩
  pushout.desc (CartesianMonoidalCategory.lift (𝟙 _) (𝒞.χ₀ _ ≫ 𝒞.truth))
    (CartesianMonoidalCategory.lift (𝒞.χ₀ _ ≫ 𝒞.truth) (𝟙 _)) (by
    apply CartesianMonoidalCategory.hom_ext <;> simp [Subsingleton.elim (𝒞.χ₀ _) (𝟙 _)])

noncomputable def Classifier.or_aux'
    [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] (𝒞 : Classifier C) :
    letI : HasClassifier C := ⟨⟨𝒞⟩⟩
    coprod 𝒞.Ω 𝒞.Ω ⟶ (𝒞.Ω ⊗ 𝒞.Ω) :=
  letI : HasClassifier C := ⟨⟨𝒞⟩⟩
  CartesianMonoidalCategory.lift (coprod.desc (𝟙 _) (𝒞.χ₀ _ ≫ 𝒞.truth)) (
    coprod.desc (𝒞.χ₀ _ ≫ 𝒞.truth) (𝟙 _))
  -- )
  --   (CartesianMonoidalCategory.lift (𝒞.χ₀ _ ≫ 𝒞.truth) (𝟙 _)) (by
  --   apply CartesianMonoidalCategory.hom_ext <;> simp [Subsingleton.elim (𝒞.χ₀ _) (𝟙 _)])


noncomputable def Classifier.or [CartesianMonoidalCategory C] [MonoidalClosed C]
    [HasFiniteLimits C] (𝒞 : Classifier C)
    [MonoidalClosed C] : 𝒞.Ω ⊗ 𝒞.Ω ⟶ 𝒞.Ω :=
  letI : HasClassifier C := ⟨⟨𝒞⟩⟩
  𝒞.χ (Topos.imageFactorization <| 𝒞.or_aux).F.m

noncomputable def Classifier.or' [CartesianMonoidalCategory C] [MonoidalClosed C]
    [HasFiniteLimits C] (𝒞 : Classifier C)
    [MonoidalClosed C] : 𝒞.Ω ⊗ 𝒞.Ω ⟶ 𝒞.Ω :=
  letI : HasClassifier C := ⟨⟨𝒞⟩⟩
  𝒞.χ (Topos.imageFactorization <| 𝒞.or_aux').F.m

attribute [local instance] CategoryTheory.BraidedCategory.ofCartesianMonoidalCategory in
lemma Classifier.or_comm_aux
    [CartesianMonoidalCategory C] [MonoidalClosed C] (𝒞 : Classifier C)
    [HasFiniteLimits C] :
    (β_ _ _).hom ≫ 𝒞.or = 𝒞.or := by
  have : HasClassifier C := ⟨⟨𝒞⟩⟩
  dsimp [Classifier.or]
  let z : MonoFactorisation (𝒞.or_aux) := {
    I := (Topos.imageFactorization 𝒞.or_aux).F.I
    m := (Topos.imageFactorization 𝒞.or_aux).F.m ≫ (β_ _ _).hom
    m_mono := inferInstance
    e := (pushoutSymmetry (𝒞.truth) (𝒞.truth)).hom ≫ (Topos.imageFactorization 𝒞.or_aux).F.e
    fac := by
      apply pushout.hom_ext <;> simp [Classifier.or_aux]
  }
  apply 𝒞.uniq (Topos.imageFactorization 𝒞.or_aux).F.m (χ₀' :=
    (Topos.imageFactorization 𝒞.or_aux).isImage.lift z ≫ 𝒞.χ₀ _)
  apply IsPullback.paste_vert _ (𝒞.isPullback _)
  apply @IsPullback.of_vert_isIso_mono _ _ _ _ _ _ _ _ _ _ ?_ _ ⟨?_⟩
  · use (Topos.imageFactorization 𝒞.or_aux).isImage.lift z
    rw [← cancel_mono (z.m)]
    simp only [Category.assoc, IsImage.lift_fac, Category.id_comp, and_self]
    rw [← cancel_mono (β_ _ _).hom,Category.assoc, IsImage.lift_fac]
    unfold z
    rw [Category.assoc,SymmetricCategory.symmetry,Category.comp_id]
  · rw [← cancel_mono (β_ _ _).hom,Category.assoc,Category.assoc,
      IsImage.lift_fac,SymmetricCategory.symmetry,Category.comp_id]

lemma Classifier.or_comm [CartesianMonoidalCategory C] [MonoidalClosed C] (𝒞 : Classifier C)
    [HasFiniteLimits C] {X : C} (f g : X ⟶ 𝒞.Ω) :
    CartesianMonoidalCategory.lift f g ≫ 𝒞.or = CartesianMonoidalCategory.lift g f ≫ 𝒞.or := by
  nth_rw 1 [← 𝒞.or_comm_aux]
  simp

lemma Classifier.or_assoc_aux [CartesianMonoidalCategory C] [MonoidalClosed C] (𝒞 : Classifier C)
    [HasFiniteLimits C] :
    (α_ _ _ _).hom ≫ (𝒞.Ω ◁ 𝒞.or) ≫ 𝒞.or = (𝒞.or ▷ 𝒞.Ω) ≫ 𝒞.or := by

  sorry
  -- apply 𝒞.hom_ext _ _ (m := ((𝒞.truth) ⊗ₘ 𝒞.truth) ⊗ₘ (𝒞.truth))
  -- · have assoc : IsPullback ((𝒞.truth ⊗ₘ 𝒞.truth) ⊗ₘ 𝒞.truth)
  --       (α_ _ _ _).hom (α_ _ _ _).hom
  --       (𝒞.truth ⊗ₘ (𝒞.truth ⊗ₘ 𝒞.truth)) := by
  --     exact .of_vert_isIso_mono (by simp)
  --   have := ((IsPullback.id_vert 𝒞.truth).tensor 𝒞.and_isPullback).paste_vert 𝒞.and_isPullback
  --   exact assoc.paste_vert this
  -- · exact (𝒞.and_isPullback.tensor (IsPullback.id_vert 𝒞.truth)).paste_vert 𝒞.and_isPullback


end or



open MonoidalCategory in
noncomputable abbrev Classifier.«→» [CartesianMonoidalCategory C] (𝒞 : Classifier C)
    [HasFiniteLimits C]
    [HasEqualizer 𝒞.and (CartesianMonoidalCategory.fst _ _)] : 𝒞.Ω ⊗ 𝒞.Ω ⟶ 𝒞.Ω :=
  𝒞.χ (Limits.equalizer.ι 𝒞.and (CartesianMonoidalCategory.fst _ _))



end CategoryTheory
