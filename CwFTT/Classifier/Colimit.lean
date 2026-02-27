import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Monadicity
import Mathlib.CategoryTheory.Limits.Preserves.Creates.Finite
import Mathlib.CategoryTheory.MorphismProperty.Limits

import CwFTT.Classifier.Basic
import CwFTT.Util.Pullback
import CwFTT.Util.Cartesian
import CwFTT.Util.CartesianPullback
import CwFTT.Util.Cone


namespace CategoryTheory
open Limits
universe v u
variable {C : Type u} [Category.{v} C]

section colimits
open MonoidalCategory CartesianMonoidalCategory


variable [HasFiniteLimits C]

abbrev Topos.singleton [CartesianMonoidalCategory C] [MonoidalClosed C] (𝒞 : Classifier C)
    (X : C) : X ⟶ (MonoidalClosed.internalHom.obj (.op X)).obj 𝒞.Ω :=
  (MonoidalClosed.curry (𝒞.χ (CartesianMonoidalCategory.lift (𝟙 X) (𝟙 X))))

omit [HasFiniteLimits C] in
lemma whiskerLeft_singleton_comp_whiskerRight_eq [CartesianMonoidalCategory C] [MonoidalClosed C]
    (𝒞 : Classifier C) (X Y : C) (f : Y ⟶ X) :
    _ ◁ Topos.singleton 𝒞 X ≫ f ▷ _ ≫ (ihom.ev X).app 𝒞.Ω = 𝒞.χ (lift (𝟙 _) (f)) := by
  rw [whisker_exchange_assoc]
  unfold Topos.singleton
  rw [← MonoidalClosed.uncurry_eq,MonoidalClosed.uncurry_curry]
  apply 𝒞.uniq _ (χ₀' := f ≫ _)
  apply IsPullback.paste_vert _ (𝒞.isPullback _)
  exact IsPullback.graph f

instance [CartesianMonoidalCategory C] [MonoidalClosed C] (𝒞 : Classifier C)
    (Y : C) : Mono (Topos.singleton 𝒞 Y) where
  right_cancellation {X} f g h := by
    have := congr(MonoidalClosed.uncurry $h)
    simp only [Topos.singleton, MonoidalClosed.uncurry_natural_left,
      MonoidalClosed.uncurry_curry] at this
    have hf := IsPullback.paste_vert (IsPullback.graph' f) (𝒞.isPullback _)
    have hg := IsPullback.paste_vert (IsPullback.graph' g) (𝒞.isPullback _)
    rw [this] at hf
    obtain ⟨hl,hr⟩ :=
      CartesianMonoidalCategory.hom_ext_iff.mp (IsPullback.isoIsPullback_hom_fst _ _ hf hg)
    simp only [comp_lift, Category.comp_id, lift_snd] at hr
    rw [hr] at hl
    simpa using congr($(hl)).symm

instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [MonoidalClosed C] :
    (MonoidalClosed.internalHom.flip.obj 𝒞.Ω).Faithful where
  map_injective {Y X} f g heq := by
    simp only [Functor.flip_obj_obj, Functor.flip_obj_map] at heq
    rw [← Quiver.Hom.op_unop f,← Quiver.Hom.op_unop g] at heq
    rw [internalHom.map_app_eq,internalHom.map_app_eq] at heq
    apply MonoidalClosed.curry_injective at heq
    simp only [Opposite.op_unop, Functor.id_obj] at heq
    -- let singleton : Y.unop ⟶ (internalHom.obj Y).obj 𝒞.Ω :=
    --   MonoidalClosed.curry (𝒞.χ (lift (𝟙 _) (𝟙 _)))
    have h : 𝒞.χ (lift (𝟙 _) f.unop) = 𝒞.χ (lift (𝟙 _) g.unop) := by
      rw [← whiskerLeft_singleton_comp_whiskerRight_eq,← whiskerLeft_singleton_comp_whiskerRight_eq,
        heq]
    clear heq
    have hf := 𝒞.isPullback (lift (𝟙 _) f.unop)
    have hg := 𝒞.isPullback (lift (𝟙 _) g.unop)
    rw [← h] at hg
    obtain ⟨hl,hr⟩ :=
      CartesianMonoidalCategory.hom_ext_iff.mp (IsPullback.isoIsPullback_hom_fst _ _ hf hg)
    simp only [comp_lift, Category.comp_id, lift_fst] at hl
    rw [hl] at hr
    simpa using congr($(hr).op).symm

instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [MonoidalClosed C] :
    (MonoidalClosed.internalHom.flip.obj 𝒞.Ω).ReflectsIsomorphisms :=
    letI : HasClassifier C := ⟨⟨𝒞⟩⟩
  inferInstance

noncomputable def Classifier.exists (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    [MonoidalClosed C]
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    (MonoidalClosed.internalHom.obj (Opposite.op X)).obj (𝒞.Ω) ⟶
      (MonoidalClosed.internalHom.obj (Opposite.op Y)).obj (𝒞.Ω) :=
  MonoidalClosed.curry (𝒞.χ (
    (pullback.fst (((ihom.ev X).app 𝒞.Ω)) 𝒞.truth) ≫
      f ▷ (MonoidalClosed.internalHom.obj (Opposite.op X)).obj 𝒞.Ω))

lemma Classifier.uncurry_exists_comp_tensorRight (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    [MonoidalClosed C]
    {X Y : C} (f : X ⟶ Y) [Mono f] : (f ▷ _) ≫ MonoidalClosed.uncurry (𝒞.exists f) =
    (ihom.ev X).app 𝒞.Ω := by
  rw [Classifier.exists,MonoidalClosed.uncurry_curry]
  have := (𝒞.isPullback (pullback.fst ((ihom.ev X).app 𝒞.Ω) 𝒞.truth ≫ f ▷ _)).shift_mono_top
  exact 𝒞.hom_ext _ _ _ _ this (IsPullback.of_hasPullback _ _)

lemma Classifier.beck_condition (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    [MonoidalClosed C]
    {X Y Z T : C} {f : X ⟶ Y} {g : X ⟶ Z} [Mono g] {h : Y ⟶ T} [Mono h]
    {k : Z ⟶ T} (hf : IsPullback f g h k) :
    (MonoidalClosed.internalHom.map f.op).app 𝒞.Ω ≫ 𝒞.exists g =
      (𝒞.exists h) ≫ (MonoidalClosed.internalHom.map k.op).app 𝒞.Ω := by
  have h_exists {X' Z' : C } (g' : X' ⟶ Z') [Mono g'] :=
    𝒞.isPullback (pullback.fst ((ihom.ev X').app 𝒞.Ω) 𝒞.truth ≫
      g' ▷ (MonoidalClosed.internalHom.obj _).obj _)
  have clw' := (IsPullback.id_vert g).tensor (IsPullback.id_horiz
    ((MonoidalClosed.internalHom.map f.op).app 𝒞.Ω))
  simp only [id_tensorHom, tensorHom_id] at clw' -- cclw'
  have clw := ((IsPullback.of_hasPullback
    _ (pullback.fst (((ihom.ev X).app 𝒞.Ω)) 𝒞.truth)).paste_horiz clw').paste_vert (h_exists g)
  have clw₂ := clw.shift_mono_top
  rw [← whisker_exchange_assoc g ((MonoidalClosed.internalHom.map f.op).app 𝒞.Ω)] at clw₂
  rw [← MonoidalClosed.uncurry_curry (𝒞.χ _),← Classifier.exists.eq_1,
    Classifier.uncurry_exists_comp_tensorRight,← MonoidalClosed.uncurry_eq,
    uncurry_internalHom_map_app] at clw₂
  let lft : pullback (X ◁ (MonoidalClosed.internalHom.map f.op).app _)
      (pullback.fst ((ihom.ev X).app 𝒞.Ω) 𝒞.truth) ⟶
        (pullback ((ihom.ev Y).app 𝒞.Ω) 𝒞.truth) := by
    refine pullback.lift ?_ ?_ ?_
    · refine pullback.fst _ _ ≫ (f ▷ (MonoidalClosed.internalHom.obj (Opposite.op Y)).obj 𝒞.Ω)
    · exact 𝒞.χ₀ _
    · simp only [Functor.comp_obj, curriedTensor_obj_obj, Functor.id_obj, Category.assoc]
      rw [← uncurry_internalHom_map_app,MonoidalClosed.uncurry_eq]
      simp only
      rw [pullback.condition_assoc,pullback.condition,← Category.assoc]
      congr
      exact Subsingleton.elim _ _
  have small : IsPullback (pullback.fst _ _) (lft)
      (f ▷ ((MonoidalClosed.internalHom.obj (Opposite.op Y)).obj 𝒞.Ω))
      (pullback.fst _ _) := by
      apply IsPullback.of_bot _ _ (h_exists h).shift_mono_top
      · rw [Subsingleton.elim (lft ≫ 𝒞.χ₀ _) (_ ≫ 𝒞.χ₀ _),Classifier.comp_χ_comp,
          Classifier.χ_pullback_fst]
        exact clw₂
      · unfold lft
        rw [pullback.lift_fst]
  have cclw' := hf.flip.tensor (IsPullback.id_vert
    (𝟙 (MonoidalClosed.internalHom.obj (Opposite.op Y)).obj 𝒞.Ω))
  simp only [Pi.id_apply, tensorHom_id] at cclw'
  have cclw := (small.paste_horiz cclw').paste_vert (h_exists h)
  rw [Subsingleton.elim (_ ≫ 𝒞.χ₀ _) (𝒞.χ₀ _)] at cclw clw₂
  clear small lft cclw' clw₂ clw' h_exists -- cleanup
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left,MonoidalClosed.uncurry_natural_left]
  simp only
  rw [uncurry_internalHom_map_app,Classifier.exists,MonoidalClosed.uncurry_curry]
  rw [whisker_exchange_assoc,← MonoidalClosed.uncurry_eq,
    Classifier.exists,MonoidalClosed.uncurry_curry]
  exact Classifier.hom_ext _ _ _ _ _ clw cclw

lemma Classifier.exists_comp_internalHom_eq (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    [MonoidalClosed C]
    {X Y : C} (f : X ⟶ Y) [Mono f] : 𝒞.exists f ≫
      (MonoidalClosed.internalHom.map f.op).app 𝒞.Ω = 𝟙 _ := by
  have := 𝒞.beck_condition (IsPullback.of_vert_isIso_mono (show
    CommSq (𝟙 X) (𝟙 X) f f from by simp))
  simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp] at this
  rw [Classifier.exists] at this
  simp only [Functor.comp_obj, curriedTensor_obj_obj, Functor.id_obj, id_whiskerRight] at this
  apply MonoidalClosed.uncurry_injective
  apply congrArg (MonoidalClosed.uncurry) at this
  trans (ihom.ev _).app _
  · simp only [MonoidalClosed.uncurry_curry] at this
    rw [← this]
    trans 𝒞.χ (pullback.fst ((ihom.ev X).app 𝒞.Ω) 𝒞.truth)
    · congr
      erw [@Category.comp_id _ _]
    · rw [𝒞.χ_pullback_fst]
  rw [MonoidalClosed.uncurry_eq]
  simp

omit [HasFiniteLimits C] in
lemma IsReflexivePair.epi_left {X Y : C} {f g : X ⟶ Y} (h : IsReflexivePair f g) :
    Epi f where
  left_cancellation {Z} h₁ h₂ heq := by
    simpa [reassoc_of% h.common_section.choose_spec.left] using
      congr(h.common_section.choose ≫ $heq)

omit [HasFiniteLimits C] in
lemma IsReflexivePair.epi_right {X Y : C} {f g : X ⟶ Y} (h : IsReflexivePair f g) :
    Epi g := h.swap.epi_left


instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [MonoidalClosed C] :
    Monad.PreservesColimitOfIsReflexivePair (MonoidalClosed.internalHom.flip.obj 𝒞.Ω) where
  out {Z Y} g h hd' := {
    preserves {c} hc := by
      change Cofork g h at c
      -- let d : Y ⟶ Z := hfg.common_section.choose
      have hd := hd'.common_section.choose_spec
      generalize hd'.common_section.choose = d at *
      have := hd'.epi_left
      have := hd'.epi_right
      have hpushout : IsPushout h g (c.π) (c.π) := by
        refine ⟨⟨(c.condition.symm)⟩,⟨?_⟩⟩
        refine PushoutCocone.IsColimit.mk _ (fun c'=> Cofork.IsColimit.desc hc c'.inl ?_) ?_ ?_ ?_
        · rw [c'.condition,← Category.id_comp c'.inl]
          simp only [← hd.right, Category.assoc, c'.condition,
            reassoc_of% hd.left]
        · intro c'
          simp only [Functor.const_obj_obj, Cofork.IsColimit.π_desc']
        · intro c'
          apply this.left_cancellation
          simp only [Functor.const_obj_obj, Cofork.IsColimit.π_desc']
          rw [← Category.id_comp c'.inl]
          simp only [← hd.right, Category.assoc, c'.condition,
            reassoc_of% hd.left]
        · intro c' m hm₁ hm₂
          simp only [Functor.const_obj_obj]
          apply Cofork.IsColimit.hom_ext hc
          rw [hm₁,Cofork.IsColimit.π_desc']
      have hpullback := hpushout.unop
      clear hd' -- maybe not, could be useful later
      have hpi : Mono c.π.unop := hpullback.mono_fst
      have := 𝒞.beck_condition hpullback.flip
      constructor
      let isoFunc : parallelPair g h ⋙ (MonoidalClosed.internalHom.flip.obj 𝒞.Ω) ≅
        (parallelPair ((MonoidalClosed.internalHom.map g).app 𝒞.Ω)
          ((MonoidalClosed.internalHom.map h).app 𝒞.Ω)) := by
        refine parallelPair.ext (Iso.refl _) (Iso.refl _) ?_ ?_
        · simp only [Functor.comp_obj, parallelPair_obj_zero, Functor.flip_obj_obj,
            parallelPair_obj_one, Functor.comp_map, parallelPair_map_left, Functor.flip_obj_map,
            Iso.refl_hom, Category.comp_id, Category.id_comp]
        · rw [Functor.comp_map,parallelPair_map_right, parallelPair_map_right]
          simp
      refine Limits.IsColimit.precomposeHomEquiv isoFunc.symm _ ?_
      refine Cofork.IsColimit.ofSplitting _ (𝒞.exists (c.π.unop)) ?_ (𝒞.exists g.unop) ?_ ?_
      · unfold Cofork.π isoFunc
        simpa using 𝒞.exists_comp_internalHom_eq c.π.unop
      · apply Classifier.exists_comp_internalHom_eq
      · unfold isoFunc Cofork.π
        simpa using (𝒞.beck_condition hpullback).symm}

instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [MonoidalClosed C] :
    MonadicRightAdjoint (MonoidalClosed.internalHom.flip.obj 𝒞.Ω) :=
  letI inst := BraidedCategory.ofCartesianMonoidalCategory
  CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms
    (@MonoidalClosed.internalHom.flip_adjoint C _ _ _ inst 𝒞.Ω)

noncomputable instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [MonoidalClosed C] :
    CreatesLimits (MonoidalClosed.internalHom.flip.obj 𝒞.Ω) :=
  monadicCreatesLimits (MonoidalClosed.internalHom.flip.obj 𝒞.Ω)

instance [HasClassifier C] [CartesianMonoidalCategory C] [MonoidalClosed C] :
    HasFiniteLimits Cᵒᵖ :=
  hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits
    (MonoidalClosed.internalHom.flip.obj (Classifier.Ω
      (Classical.choice HasClassifier.exists_classifier)))

instance [HasClassifier C] [CartesianMonoidalCategory C] [MonoidalClosed C] :
    HasFiniteColimits C where
      out _ _ _ := hasColimitsOfShape_of_hasLimitsOfShape_op


end colimits
end CategoryTheory
