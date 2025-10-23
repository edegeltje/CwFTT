import Mathlib.CategoryTheory.Topos.Classifier
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.OfHasFiniteProducts
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monad.Monadicity
import CwFTT.Util.Pullback
import CwFTT.Util.Cartesian
import CwFTT.Util.CartesianPullback

namespace CategoryTheory
open Limits
universe v u
variable {C : Type u} [Category.{v} C]

/- these lemmas should really be in Topos.Classifier or something -/
section

instance (𝒞 : Classifier C) (X : C) : HasBinaryProduct 𝒞.Ω₀ X where
  exists_limit := ⟨⟨BinaryFan.mk (𝒞.χ₀ X) (𝟙 X),by
    apply Classical.choice
    rw [BinaryFan.isLimit_iff_isIso_snd (𝒞.isTerminalΩ₀)]
    simpa using IsIso.id X
    ⟩
  ⟩

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

-- lemma Classifier.hom_ext_iff (𝒞 : Classifier C) {X : C} (f g : X ⟶ 𝒞.Ω) (m : ) :
--     f = g ↔ IsPullback (pullback.fst g 𝒞.truth) (𝒞.χ₀ _) f 𝒞.truth := by
--   refine ⟨?_,𝒞.hom_ext f g _⟩
--   intro heq
--   convert IsPullback.of_hasPullback g 𝒞.truth
--   exact Subsingleton.elim _ _

@[reassoc (attr := simp)]
lemma Classifier.comp_χ₀ (𝒞 : Classifier C) {X Y : C} (m : X ⟶ Y) :
  m ≫ 𝒞.χ₀ _ = 𝒞.χ₀ _ := Subsingleton.elim _ _

lemma Classifier.χ_pullback_fst (𝒞 : Classifier C) {X : C} (a : X ⟶ 𝒞.Ω) [HasPullback a 𝒞.truth] :
  𝒞.χ (pullback.fst a 𝒞.truth) = a := by
  symm
  apply 𝒞.uniq
  exact .of_hasPullback _ _

end
section and
noncomputable abbrev Classifier.and (𝒞 : Classifier C) [HasBinaryProduct 𝒞.Ω 𝒞.Ω] :
    𝒞.Ω ⨯ 𝒞.Ω ⟶ 𝒞.Ω :=
  𝒞.χ (Limits.prod.map 𝒞.truth 𝒞.truth)

lemma Classifier.and_isPullback (𝒞 : Classifier C) [HasBinaryProduct 𝒞.Ω 𝒞.Ω] :
    IsPullback (prod.map 𝒞.truth 𝒞.truth) (𝒞.χ₀ _) (𝒞.and) (𝒞.truth) := 𝒞.isPullback _

lemma Classifier.χ_pullback [HasBinaryProducts C] {𝒞 : Classifier C} {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} [Mono f₃] {f₄ : X₃ ⟶ X₄} [Mono f₄]
    (hf : IsPullback f₁ f₂ f₃ f₄) :
    letI : Mono (f₁ ≫ f₃) := mono_comp' (hf.mono_fst) inferInstance
    𝒞.χ (f₁ ≫ f₃) = Limits.prod.lift (𝒞.χ f₃) (𝒞.χ f₄) ≫ 𝒞.and := by
  symm
  have : Mono (f₁ ≫ f₃) := mono_comp' (hf.mono_fst) inferInstance
  refine 𝒞.uniq _ (χ₀' := 𝒞.χ₀ _) ?_
  rw [Classifier.truth]
  convert IsPullback.paste_vert (IsPullback.pullback_fst (𝒞.isPullback f₃) (𝒞.isPullback f₄) hf)
    (𝒞.isPullback (Limits.prod.map 𝒞.truth 𝒞.truth))

  apply Subsingleton.elim

lemma Classifier.and_comm_aux (𝒞 : Classifier C) [HasBinaryProduct 𝒞.Ω 𝒞.Ω] :
    (prod.braiding _ _).hom ≫ 𝒞.and = 𝒞.and := by
  dsimp [Classifier.and]
  apply 𝒞.uniq _ (χ₀' := (prod.braiding _ _).hom ≫ 𝒞.χ₀ _)
  have : IsPullback (prod.map 𝒞.truth 𝒞.truth)
      (prod.braiding _ _).hom (prod.braiding _ _).hom (prod.map 𝒞.truth 𝒞.truth) := by
    exact .of_vert_isIso_mono (by simp)
  exact (this).paste_vert (𝒞.isPullback (prod.map 𝒞.truth 𝒞.truth))

lemma Classifier.and_comm (𝒞 : Classifier C) [HasBinaryProduct 𝒞.Ω 𝒞.Ω] {X : C} (f g : X ⟶ 𝒞.Ω) :
    prod.lift f g ≫ 𝒞.and = prod.lift g f ≫ 𝒞.and := by
  nth_rw 1 [← 𝒞.and_comm_aux]
  simp only [prod.braiding_hom, ← Category.assoc]
  congr
  ext <;> simp

lemma Classifier.and_assoc_aux (𝒞 : Classifier C) [HasBinaryProducts C] :
    (prod.associator ..).hom ≫ prod.map (𝟙 _) (𝒞.and) ≫ 𝒞.and = prod.map (𝒞.and) (𝟙 _) ≫ 𝒞.and := by
  apply 𝒞.hom_ext _ _ (m := prod.map (prod.map (𝒞.truth) 𝒞.truth) (𝒞.truth))
  · have assoc : IsPullback (prod.map (prod.map 𝒞.truth 𝒞.truth) 𝒞.truth)
        (prod.associator _ _ _).hom (prod.associator _ _ _).hom
        (prod.map 𝒞.truth (prod.map 𝒞.truth 𝒞.truth)) := by
      exact .of_vert_isIso_mono (by simp)
    have := ((IsPullback.id_vert 𝒞.truth).prod 𝒞.and_isPullback).paste_vert 𝒞.and_isPullback
    exact assoc.paste_vert this
  · exact (𝒞.and_isPullback.prod (IsPullback.id_vert 𝒞.truth)).paste_vert 𝒞.and_isPullback

lemma Classifier.and_assoc (𝒞 : Classifier C) [HasBinaryProducts C] {X : C} (f g h : X ⟶ 𝒞.Ω) :
    prod.lift (prod.lift f g ≫ 𝒞.and) h ≫ 𝒞.and = prod.lift f (prod.lift g h ≫ 𝒞.and) ≫ 𝒞.and := by
  trans prod.lift (prod.lift f g) h ≫ prod.map 𝒞.and (𝟙 _) ≫ 𝒞.and
  · simp
  · rw [← 𝒞.and_assoc_aux]
    simp [← Category.assoc]
end and

section colimits
open MonoidalCategory CartesianMonoidalCategory


variable [HasFiniteLimits C]

instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [CartesianClosed C] :
    (internalHom.flip.obj 𝒞.Ω).Faithful where
  map_injective {Y X} f g heq := by
    simp only [Functor.flip_obj_obj, Functor.flip_obj_map] at heq
    rw [← Quiver.Hom.op_unop f,← Quiver.Hom.op_unop g] at heq
    rw [internalHom.map_app_eq,internalHom.map_app_eq] at heq
    apply CartesianClosed.curry_injective at heq
    simp only [Opposite.op_unop, Functor.id_obj] at heq
    let singleton : Y.unop ⟶ (internalHom.obj Y).obj 𝒞.Ω :=
      CartesianClosed.curry (𝒞.χ (lift (𝟙 _) (𝟙 _)))

    have (f' : X.unop ⟶ Y.unop) :
        _ ◁ singleton ≫ f' ▷ _ ≫ (exp.ev Y.unop).app 𝒞.Ω =
          𝒞.χ (lift (𝟙 _) (f')) := by
      rw [whisker_exchange_assoc]
      unfold singleton
      rw [← CartesianClosed.uncurry_eq,CartesianClosed.uncurry_curry]
      apply 𝒞.uniq _ (χ₀' := f' ≫ _)
      apply IsPullback.paste_vert _ (𝒞.isPullback _)
      refine IsPullback.of_isLimit' (by simp) (PullbackCone.IsLimit.mk _
        (fun s => s.fst ≫ fst _ _)
        (by
          intro s
          apply CartesianMonoidalCategory.hom_ext
          · simp
          simp only [comp_lift, Category.comp_id, Category.assoc, lift_snd]
          rw [← whiskerRight_fst,← whiskerRight_snd f', s.condition_assoc, s.condition_assoc,
            lift_fst,lift_snd])
          (by
            intro s
            simp only [Category.assoc]
            rw [← whiskerRight_fst,s.condition_assoc,lift_fst,Category.comp_id])
          (by
            intro s m hm₁ _
            simp only [comp_lift, Category.comp_id] at hm₁ ⊢
            rw [← hm₁]
            simp only [lift_fst]))

    have h : 𝒞.χ (lift (𝟙 _) f.unop) = 𝒞.χ (lift (𝟙 _) g.unop) := by
      rw [← this,← this,heq]
    clear heq this singleton
    have hf := 𝒞.isPullback (lift (𝟙 _) f.unop)
    have hg := 𝒞.isPullback (lift (𝟙 _) g.unop)
    rw [← h] at hg
    obtain ⟨hl,hr⟩ :=
      CartesianMonoidalCategory.hom_ext_iff.mp (IsPullback.isoIsPullback_hom_fst _ _ hf hg)
    simp only [comp_lift, Category.comp_id, lift_fst] at hl
    rw [hl] at hr
    simpa using congr($(hr).op).symm


instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [CartesianClosed C] :
    (internalHom.flip.obj 𝒞.Ω).ReflectsIsomorphisms :=
    letI : HasClassifier C := ⟨⟨𝒞⟩⟩
  inferInstance



noncomputable def Classifier.exists (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    [CartesianClosed C]
    {X Y : C} (f : X ⟶ Y) [Mono f] :
    (internalHom.obj (Opposite.op X)).obj (𝒞.Ω) ⟶ (internalHom.obj (Opposite.op Y)).obj (𝒞.Ω) :=
  CartesianClosed.curry (𝒞.χ (
    (pullback.fst (((exp.ev X).app 𝒞.Ω)) 𝒞.truth) ≫ f ▷ (internalHom.obj (Opposite.op X)).obj 𝒞.Ω))

lemma Classifier.uncurry_exists_comp_tensorRight (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    [CartesianClosed C]
    {X Y : C} (f : X ⟶ Y) [Mono f] : (f ▷ _) ≫ CartesianClosed.uncurry (𝒞.exists f) =
    (exp.ev X).app 𝒞.Ω := by
  rw [Classifier.exists,CartesianClosed.uncurry_curry]
  have := (𝒞.isPullback (pullback.fst ((exp.ev X).app 𝒞.Ω) 𝒞.truth ≫ f ▷ _)).shift_mono_top
  exact 𝒞.hom_ext _ _ _ _ this (IsPullback.of_hasPullback _ _)

lemma beck_condition (𝒞 : Classifier C) [CartesianMonoidalCategory C]
    [CartesianClosed C]
    {X Y Z T : C} {f : X ⟶ Y} {g : X ⟶ Z} [Mono g] {h : Y ⟶ T} [Mono h]
    {k : Z ⟶ T} (hf : IsPullback f g h k) :
    (internalHom.map f.op).app 𝒞.Ω ≫ 𝒞.exists g =
      (𝒞.exists h) ≫ (internalHom.map k.op).app 𝒞.Ω := by
  have h_exists {X' Z' : C } (g' : X' ⟶ Z') [Mono g'] :=
    𝒞.isPullback (pullback.fst ((exp.ev X').app 𝒞.Ω) 𝒞.truth ≫ g' ▷ (internalHom.obj _).obj _)
  have clw' := (IsPullback.id_vert g).tensor (IsPullback.id_horiz ((internalHom.map f.op).app 𝒞.Ω))
  simp only [id_tensorHom, tensorHom_id] at clw' -- cclw'
  have clw := ((IsPullback.of_hasPullback
    _ (pullback.fst (((exp.ev X).app 𝒞.Ω)) 𝒞.truth)).paste_horiz clw').paste_vert (h_exists g)
  have clw₂ := clw.shift_mono_top
  rw [← whisker_exchange_assoc g ((internalHom.map f.op).app 𝒞.Ω)] at clw₂
  rw [← CartesianClosed.uncurry_curry (𝒞.χ _),← Classifier.exists.eq_1,
    Classifier.uncurry_exists_comp_tensorRight,← CartesianClosed.uncurry_eq,
    uncurry_internalHom_map_app] at clw₂
  let lft : pullback (X◁ (internalHom.map f.op).app _) (pullback.fst ((exp.ev X).app 𝒞.Ω) 𝒞.truth) ⟶
      (pullback ((exp.ev Y).app 𝒞.Ω) 𝒞.truth) := by
    refine pullback.lift ?_ ?_ ?_
    · refine pullback.fst _ _ ≫ (f ▷ (internalHom.obj (Opposite.op Y)).obj 𝒞.Ω)
    · exact 𝒞.χ₀ _
    · simp
      rw [← uncurry_internalHom_map_app,CartesianClosed.uncurry_eq]
      simp only
      rw [pullback.condition_assoc,pullback.condition,← Category.assoc]
      congr
      exact Subsingleton.elim _ _
  have small : IsPullback (pullback.fst _ _) (lft)
      (f ▷ ((internalHom.obj (Opposite.op Y)).obj 𝒞.Ω))
      (pullback.fst _ _) := by
      apply IsPullback.of_bot _ _ (h_exists h).shift_mono_top
      · rw [Subsingleton.elim (lft ≫ 𝒞.χ₀ _) (_ ≫ 𝒞.χ₀ _),Classifier.comp_χ_comp,
          Classifier.χ_pullback_fst]
        exact clw₂
      · unfold lft
        rw [pullback.lift_fst]
  have cclw' := hf.flip.tensor (IsPullback.id_vert
    (𝟙 (internalHom.obj (Opposite.op Y)).obj 𝒞.Ω))
  simp only [Pi.id_apply, tensorHom_id] at cclw'
  have cclw := (small.paste_horiz cclw').paste_vert (h_exists h)
  rw [Subsingleton.elim (_ ≫ 𝒞.χ₀ _) (𝒞.χ₀ _)] at cclw clw₂
  clear small lft cclw' clw₂ clw' h_exists -- cleanup
  apply CartesianClosed.uncurry_injective
  rw [CartesianClosed.uncurry_natural_left,CartesianClosed.uncurry_natural_left]
  simp only
  rw [uncurry_internalHom_map_app,Classifier.exists,CartesianClosed.uncurry_curry]
  rw [whisker_exchange_assoc,← CartesianClosed.uncurry_eq,
    Classifier.exists,CartesianClosed.uncurry_curry]
  exact Classifier.hom_ext _ _ _ _ _ clw cclw

instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [CartesianClosed C] :
    Monad.PreservesColimitOfIsReflexivePair (internalHom.flip.obj 𝒞.Ω) where
  out {A B} f g hfg := sorry

-- instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [CartesianClosed C] :
--     Monad.PreservesColimitOfIsSplitPair (internalHom.flip.obj 𝒞.Ω) := sorry

instance (𝒞 : Classifier C) [CartesianMonoidalCategory C] [CartesianClosed C] :
    MonadicRightAdjoint (internalHom.flip.obj 𝒞.Ω) :=
  letI inst := BraidedCategory.ofCartesianMonoidalCategory
  CategoryTheory.Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms
    (@CartesianClosed.internalHom.flip_adjoint C _ _ inst _ 𝒞.Ω)
end colimits



-- don't worry about this for now
noncomputable abbrev Classifier.«→» (𝒞 : Classifier C) [HasFiniteLimits C]
    [HasEqualizer 𝒞.and Limits.prod.fst] : 𝒞.Ω ⨯ 𝒞.Ω ⟶ 𝒞.Ω :=
  𝒞.χ (Limits.equalizer.ι 𝒞.and Limits.prod.fst)



end CategoryTheory
