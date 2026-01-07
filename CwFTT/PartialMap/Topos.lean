import CwFTT.Classifier.Ops
import CwFTT.PartialMap.Classifier
import CwFTT.PartialMap.Basic

import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.CategoryTheory.LocallyCartesianClosed.ChosenPullbacksAlong


universe v u
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
  [Limits.HasFiniteLimits C]
  (𝒞 : Classifier C)
open Limits MonoidalCategory MonoidalClosed

omit [HasFiniteLimits C] in
lemma remark {U X Y : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    f ≫ (CartesianMonoidalCategory.lift (𝟙 Y) (Topos.singleton 𝒞 Y)) =
    (CartesianMonoidalCategory.lift f m) ≫
      (Y ◁ (curry (𝒞.χ (CartesianMonoidalCategory.lift f m)) ≫ eqToHom (by rfl))) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp
  · simp only [CartesianMonoidalCategory.comp_lift, Category.comp_id,
    CartesianMonoidalCategory.lift_snd, eqToHom_refl, CartesianMonoidalCategory.lift_whiskerLeft]
    apply uncurry_injective
    simp only [uncurry_natural_left, uncurry_curry]
    refine 𝒞.hom_ext _ _ (m := CartesianMonoidalCategory.graph' f) (f ≫ 𝒞.χ₀ _) (𝟙 _ ≫ 𝒞.χ₀ _)
      ?_ ?_
    · exact (IsPullback.graph' f).paste_vert (𝒞.isPullback _)
    · apply IsPullback.paste_vert _ (𝒞.isPullback _)
      · rw [CartesianMonoidalCategory.graph']
        rw [← Category.id_comp f]
        nth_rw 2 [← Category.comp_id (𝟙 U)]
        nth_rw 2 [← Category.id_comp m]
        rw [← CartesianMonoidalCategory.lift_map,← CartesianMonoidalCategory.lift_map]
        apply IsPullback.paste_horiz
        · exact IsPullback.id_vert _
        · rw [← id_tensorHom]
          convert IsPullback.tensor (.id_vert f) ((mono_iff_isPullback m).mp ‹Mono m›)
          simp
      -- sorry
    -- sorry
omit [HasFiniteLimits C] in
lemma remark2 {U X Y : C} (m : U ⟶ X) [Mono m] (f : U ⟶ Y) :
    IsPullback m f (curry (𝒞.χ (CartesianMonoidalCategory.lift f m))) (Topos.singleton 𝒞 Y) where
  w := by
    have := congr($(remark 𝒞 m f) ≫ CartesianMonoidalCategory.snd _ _)
    simpa using this.symm
  isLimit' := by
    constructor
    apply PullbackCone.IsLimit.mk _ (fun s => by
      apply (𝒞.isPullback (CartesianMonoidalCategory.lift f m)).lift
        (CartesianMonoidalCategory.lift s.snd s.fst) (𝒞.χ₀ _)
      have := congr(uncurry $(s.condition))
      simp only [uncurry_natural_left, uncurry_curry] at this
      rw [← Category.id_comp s.fst, ← Category.comp_id s.snd,←
        CartesianMonoidalCategory.lift_map_assoc,id_tensorHom,this]
      simp only [CartesianMonoidalCategory.lift_whiskerLeft_assoc, Category.id_comp]
      rw [← Category.comp_id s.snd,← CartesianMonoidalCategory.comp_lift_assoc,
        (𝒞.isPullback _).w]
      simp
      )
    · intro s
      generalize_proofs _ h1 h2
      simpa using congr($(h1.lift_fst _ _ h2) ≫ CartesianMonoidalCategory.snd _ _)
    · intro s
      generalize_proofs _ h1 h2
      simpa using congr($(h1.lift_fst _ _ h2) ≫ CartesianMonoidalCategory.fst _ _)
    · intro s m' hm₁ hm₂
      generalize_proofs _ h1 h2
      apply h1.hom_ext
      · ext
        · simpa [hm₂] using congr($(h1.lift_fst _ _ h2) ≫ CartesianMonoidalCategory.fst _ _).symm
        · simpa [hm₁] using congr($(h1.lift_fst _ _ h2) ≫ CartesianMonoidalCategory.snd _ _).symm
      · simp

-- @[simps]
noncomputable def Topos.partialMapClassifier (Y : C) : PartialMap.Classifier Y where
  obj := equalizer (MonoidalClosed.curry
    (𝒞.χ (CartesianMonoidalCategory.graph (Topos.singleton 𝒞 Y))))
      (𝟙 _)
  η := equalizer.lift (Topos.singleton 𝒞 Y) (by
    simp only [Category.comp_id]
    apply uncurry_injective
    rw [MonoidalClosed.uncurry_natural_left]
    simp only [uncurry_curry]
    refine 𝒞.hom_ext _ _ (𝟙 Y ≫ 𝒞.χ₀ _) _ ?_ (𝒞.isPullback _)
    apply IsPullback.paste_vert _ (𝒞.isPullback _)
    exact IsPullback.of_vert_isIso_mono (by simp))
  isMono := mono_of_mono_fac (equalizer.lift_ι _ _)
  χ {U X} f m _ := equalizer.lift (curry (𝒞.χ
    (CartesianMonoidalCategory.lift f m))) (by
      rw [Category.comp_id]
      apply uncurry_injective
      simp only [uncurry_natural_left, uncurry_curry]
      apply 𝒞.uniq _ (χ₀' := f ≫ 𝒞.χ₀ Y)
      apply IsPullback.paste_vert _ (𝒞.isPullback _)
      have := IsPullback.whiskerLeft_horiz (curry (𝒞.χ (CartesianMonoidalCategory.lift f m))) Y
      apply IsPullback.of_right _ (by simpa using (remark 𝒞 m f).symm) this.flip
      simp only [CartesianMonoidalCategory.lift_snd]
      exact remark2 𝒞 m f
      )
  isPullback {U X} f m _ := by
    generalize_proofs _ _ hη h2 h3
    have := remark2 𝒞 m f
    rw [← equalizer.lift_ι _ h3] at this
    rw [← equalizer.lift_ι _ h2] at this
    exact this.of_comp_of_mono
  uniq {U X} f m _ χ' hχ' := by
    generalize_proofs _ _ _ h1
    apply equalizer.hom_ext
    rw [equalizer.lift_ι _ h1, ← Category.comp_id (equalizer.ι _ _), ← equalizer.condition]
    rw [eq_curry_iff,uncurry_natural_left,uncurry_natural_left,uncurry_curry]
    simp only
    apply 𝒞.uniq _ (χ₀' := f ≫ 𝒞.χ₀ _)
    rw [← Category.assoc]
    apply IsPullback.paste_vert _ (𝒞.isPullback _)
    rw [← whiskerLeft_comp]
    apply IsPullback.of_right _ (by simp [hχ'.w]) (IsPullback.whiskerLeft_horiz (χ' ≫ _) Y).flip
    simp only [CartesianMonoidalCategory.lift_snd]
    refine ⟨⟨?_⟩,⟨?_⟩⟩
    · rw [hχ'.w_assoc,equalizer.lift_ι]
    · apply PullbackCone.IsLimit.mk _ (fun s => hχ'.lift s.fst s.snd (equalizer.hom_ext (by
        simp [← s.condition])))
      · simp
      · simp
      · intros
        apply hχ'.hom_ext <;> simpa

/-- Topoi have enough injectives -/
instance [HasClassifier C] : EnoughInjectives C where
  presentation Y := by
    obtain ⟨⟨𝒞⟩⟩ := ‹HasClassifier C›
    constructor
    refine ⟨(Topos.partialMapClassifier 𝒞 Y).obj,inferInstance,
      (Topos.partialMapClassifier 𝒞 Y).η,inferInstance⟩

/-- in a topos, pushout squares of a mono are pullbacks too -/
lemma isPullback_of_isPushout_of_mono_top [HasClassifier C] {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPushout f₁ f₂ f₃ f₄)
    (hf₁ : Mono f₁ := by infer_instance) : IsPullback f₁ f₂ f₃ f₄ := by
  obtain ⟨⟨𝒞⟩⟩ := ‹HasClassifier C›
  have pbsq := (Topos.partialMapClassifier 𝒞 _).isPullback f₂ f₁
  apply IsPullback.of_comp_of_commsq (hf.desc _ _ pbsq.w) _ hf.toCommSq
  simpa using pbsq

/-- in a topos, pushout squares of a mono are pullbacks too -/
lemma isPullback_of_isPushout_of_mono_left [HasClassifier C] {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPushout f₁ f₂ f₃ f₄)
    (hf₂ : Mono f₂ := by infer_instance) : IsPullback f₁ f₂ f₃ f₄ :=
  (isPullback_of_isPushout_of_mono_top hf.flip).flip

/-- in a topos, monos are preserved under pushout -/
lemma IsPushout.mono_inr [HasClassifier C] {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPushout f₁ f₂ f₃ f₄)
    (hf₁ : Mono f₁ := by infer_instance) : Mono f₄ := by
  obtain ⟨⟨𝒞⟩⟩ := ‹HasClassifier C›
  have pbsq := (Topos.partialMapClassifier 𝒞 _).isPullback f₂ f₁
  apply mono_of_mono_fac (hf.inr_desc _ _ pbsq.w)

/-- in a topos, monos are preserved under pushout -/
lemma IsPushout.mono_inl [HasClassifier C] {X₁ X₂ X₃ X₄ : C}
    {f₁ : X₁ ⟶ X₂} {f₂ : X₁ ⟶ X₃} {f₃ : X₂ ⟶ X₄} {f₄ : X₃ ⟶ X₄} (hf : IsPushout f₁ f₂ f₃ f₄)
    (hf₂ : Mono f₂ := by infer_instance) : Mono f₃ := hf.flip.mono_inr


section

def Classifier.over (X : C) : Classifier (Over X) where
  Ω₀ := Over.mk (CartesianMonoidalCategory.snd 𝒞.Ω₀ X)
  Ω := Over.mk (CartesianMonoidalCategory.snd 𝒞.Ω _)
  truth := Over.homMk (𝒞.truth ▷ _)
  mono_truth := inferInstance
  χ₀ U := Over.homMk (CartesianMonoidalCategory.lift (𝒞.χ₀ _) U.hom) (by simp)
  χ {U Z} m _ := Over.homMk (CartesianMonoidalCategory.lift (𝒞.χ m.left) Z.hom) (by simp)
  isPullback {U Z} m _ := by
    refine ⟨⟨?_⟩,⟨?_⟩⟩
    · ext
      apply CartesianMonoidalCategory.hom_ext <;> simp [(𝒞.isPullback _).w]
    · apply PullbackCone.IsLimit.mk _
        (fun s =>
          Over.homMk ((𝒞.isPullback m.left).lift (s.fst.left) (s.snd.left ≫ 𝒞.χ₀ _)
            (by
              have := congr($(s.condition).left ≫ CartesianMonoidalCategory.fst _ _)
              simpa [Subsingleton.elim (SemiCartesianMonoidalCategory.fst _ _) (𝒞.χ₀ _)] using this
              ))
            (by
              generalize_proofs _ h1 h2 hpb h3
              have := m.w
              simp only [Functor.id_obj, Functor.const_obj_obj, Functor.id_map,
                CostructuredArrow.right_eq_id, Functor.const_obj_map, Category.comp_id] at this
              rw [← this, hpb.lift_fst_assoc]
              simp)
        )
      · intro s;ext;simp
      · intro s
        ext
        simp only [Over.mk_left, comp_χ₀, Over.comp_left, Over.homMk_left,
          CartesianMonoidalCategory.comp_lift]
        generalize_proofs h1 h2 h3 h4 h5 h6 h7
        ext
        · simpa using Subsingleton.elim _ _
        · have := congr($(s.condition).left ≫ CartesianMonoidalCategory.snd _ _)
          simp only [Over.mk_left, Over.comp_left, Over.homMk_left,
            CartesianMonoidalCategory.comp_lift, Over.w, CartesianMonoidalCategory.lift_snd,
            Category.assoc, CartesianMonoidalCategory.whiskerRight_snd] at this ⊢
          rw [← this, ← Over.w m, h4.lift_fst_assoc,Over.w]
      · intro s m' hm₁ hm₂
        ext
        simp only [Over.mk_left, comp_χ₀, Over.homMk_left]
        generalize_proofs h1 h2 h3 h4 h5 h6
        apply h4.hom_ext
        · simpa using congr($(hm₁).left)
        · simp
  uniq {U Z} m _ χ₀' χ' hχ' := by
    ext
    simp only [Over.mk_left, Over.homMk_left]
    ext
    · simp only [CartesianMonoidalCategory.lift_fst]
      apply 𝒞.uniq _ (χ₀' := χ₀'.left ≫ CartesianMonoidalCategory.fst _ _)
      refine ⟨⟨?_⟩,⟨?_⟩⟩
      · simpa using congr($(hχ'.w).left ≫ CartesianMonoidalCategory.fst _ _)
      · refine PullbackCone.IsLimit.mk _ (fun s =>
          (hχ'.lift (W := Over.mk (s.fst ≫ χ'.left ≫
            CartesianMonoidalCategory.snd _ _))
            (Over.homMk s.fst (by simpa using congr(s.fst ≫ $(Over.w χ')).symm))
            (Over.homMk (CartesianMonoidalCategory.lift s.snd
              (s.fst ≫ χ'.left ≫ CartesianMonoidalCategory.snd _ _)))
            (by
              ext
              simp only [Over.mk_left, Over.comp_left, Over.homMk_left,
                CartesianMonoidalCategory.lift_whiskerRight]
              ext <;> simp [s.condition])).left
          ) ?_ ?_ ?_
        · intro s
          generalize_proofs h1 h2 h3 h4
          simpa [-IsPullback.lift_fst] using congr($(hχ'.lift_fst _ _ (h4 s)).left)
        · intro s
          generalize_proofs h1 h2 h3 h4
          simpa [-IsPullback.lift_snd] using congr($(hχ'.lift_snd _ _ (h4 s)).left ≫
            CartesianMonoidalCategory.fst _ _)
        · intro s m' hm₁ hm₂
          generalize_proofs h1 h2 h3 h4
          simpa [Over.mk_left, ← cancel_mono m.left, hm₁,
            -IsPullback.lift_fst] using congr($(hχ'.lift_fst _ _ (h4 s)).left).symm
    · simpa using (Over.w χ')

attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

/-
In this section, we prove the fundamental theorem of topos theory,
namely that `C` is a topos, then so is the slice category `C/X` for any X.
-/

instance [HasClassifier C] (X : C) : HasClassifier (Over X) where
  exists_classifier := by
    obtain ⟨⟨𝒞⟩⟩ := ‹HasClassifier C›
    exact ⟨𝒞.over X⟩

/-
given an object `Y : Over X`
we have a map `θ_tilde : X ⟶ exp Y.left (X_Tilde)`
additionally, for each object `Z : Over X`, we have a map
`Z_hom_tilde : Z_left_tilde ⟶ X_Tilde` (in a functorial way).
This induces a functor `Over X ⥤ Over X_Tilde`. Finally, we compose with the
pullback functor induced by `θ_tilde`




-/

noncomputable def Over.exp._θ {X : C} (Y : Over X) := (Topos.partialMapClassifier 𝒞 X).χ Y.hom
    (CartesianMonoidalCategory.graph Y.hom)

noncomputable def Over.exp._θ_tilde {X : C} (Y : Over X) :=
  curry (Over.exp._θ 𝒞 Y)

noncomputable def Over.exp._hom {X : C} (Y : Over X) :
    (Over.forget X ⋙ (PartialMap.Classifier.mkFunctor (Topos.partialMapClassifier 𝒞)) ⋙
      MonoidalClosed.internalHom.obj (.op Y.left)) ⟶ (Functor.const _).obj
    ((PartialMap.Classifier.mkFunctor (Topos.partialMapClassifier 𝒞) ⋙
      MonoidalClosed.internalHom.obj (.op Y.left)).obj X) := {
    app Z := (PartialMap.Classifier.mkFunctor (Topos.partialMapClassifier 𝒞) ⋙
      MonoidalClosed.internalHom.obj (.op Y.left)).map Z.hom
    naturality {Z₁ Z₂} f := by
      rw [Functor.comp_map,Over.forget_map,← Functor.map_comp,Functor.const_obj_map]
      simp
  }

noncomputable def Over.exp {X : C} (Y : Over X) : Over X ⥤ Over X :=
  Over.lift (Over.forget X ⋙
    (PartialMap.Classifier.mkFunctor (Topos.partialMapClassifier 𝒞)) ⋙
    (MonoidalClosed.internalHom.obj (.op Y.left)))
    (Over.exp._hom 𝒞 Y) ⋙ Over.pullback (exp._θ_tilde 𝒞 Y)

-- @[simps apply symm_apply]
-- def Over.exp.adjunction_equiv_1 {X : C} (Y : Over X) (Z₁ Z₂ : Over X) :
--     (Y ⊗ Z₁ ⟶ Z₂) ≃ {t : Limits.pullback Y.hom Z₁.hom ⟶ Z₂.left //
--       t ≫ Z₂.hom = pullback.fst _ _ ≫ Y.hom} where
--   toFun f := ⟨f.left,by simp⟩
--   invFun t := homMk (t.val) (by simp [t.property])
--   left_inv := by
--     intro f
--     ext
--     simp
--   right_inv := by
--     intro t
--     simp

-- @[simps]
-- noncomputable def Over.exp.adjunction_equiv_2 {X : C} (Y : Over X) (Z₁ Z₂ : Over X) :
--     {t : Limits.pullback Y.hom Z₁.hom ⟶ Z₂.left //
--       t ≫ Z₂.hom = pullback.fst _ _ ≫ Y.hom} ≃
--     {f : Limits.pullback
--       (CartesianMonoidalCategory.lift (𝟙 Y.left) Y.hom) (Y.left ◁ Z₁.hom) ⟶
--         Z₂.left //
--       f ≫ Z₂.hom = pullback.fst _ _ ≫ Y.hom } where
--   toFun t :=
--     let h1 := IsPullback.of_hasPullback (CartesianMonoidalCategory.lift (𝟙 Y.left) Y.hom)
--       (Y.left ◁ Z₁.hom)
--     ⟨(IsPullback.isoPullback
--       (by simpa using h1.paste_vert (IsPullback.whiskerLeft_horiz _ _))).hom ≫ t.val,
--     (by simp [t.property])⟩
--   invFun f :=
--     let h1 := IsPullback.of_hasPullback (CartesianMonoidalCategory.lift (𝟙 Y.left) Y.hom)
--       (Y.left ◁ Z₁.hom)
--     ⟨(IsPullback.isoPullback
--       (by simpa using h1.paste_vert (IsPullback.whiskerLeft_horiz _ _))).inv ≫ f.val,
--     (by simp [f.property])⟩
--   left_inv := by intro; simp
--   right_inv := by intro; simp

-- @[simps]
-- noncomputable def Over.exp.adjunction_equiv_3 {X : C} (Y : Over X) (Z₁ Z₂ : Over X) :
--     letI : Mono (CartesianMonoidalCategory.lift (𝟙 Y.left) Y.hom) :=
--       @mono_of_mono_fac _ _ _ _ _ _ _ _ (instMonoId _) (CartesianMonoidalCategory.lift_fst _ _)
--     {f : Limits.pullback
--       (CartesianMonoidalCategory.lift (𝟙 Y.left) Y.hom) (Y.left ◁ Z₁.hom) ⟶
--         Z₂.left // f ≫ Z₂.hom = pullback.fst _ _ ≫ Y.hom } ≃
--     { i_bar : Y.left ⊗ Z₁.left ⟶ (Topos.partialMapClassifier 𝒞 Z₂.left).obj //
--         i_bar ≫ (Topos.partialMapClassifier 𝒞 Z₂.left).map Z₂.hom
-- (Topos.partialMapClassifier 𝒞 X) =
--            Y.left ◁ Z₁.hom ≫ exp._θ 𝒞 Y} where
--   toFun f :=
--     ⟨((Topos.partialMapClassifier 𝒞 _).χ f.val (pullback.snd _ _)),(by
--       simp only [Functor.const_obj_obj, Functor.id_obj]
--       rw [PartialMap.Classifier.χ_comp_map]
--       symm
--       apply PartialMap.Classifier.uniq
--       rw [f.property]
--       apply IsPullback.paste_vert
--       · apply IsPullback.flip
--         exact IsPullback.of_hasPullback _ _
--       · have := mono_of_mono_fac (CartesianMonoidalCategory.lift_fst (𝟙 Y.left) Y.hom)
--         exact PartialMap.Classifier.isPullback _ _ _
--       )⟩
--   invFun i_bar := ⟨((Topos.partialMapClassifier 𝒞 X).isPullback
--     Z₂.hom (Topos.partialMapClassifier 𝒞 Z₂.left).η).lift
--       (pullback.snd _ _ ≫ i_bar.val)
--       (pullback.fst _ _ ≫ Y.hom) (by sorry),(by sorry)⟩
--   left_inv := by
--     intro f
--     ext
--     simp only [Functor.id_obj, Functor.const_obj_obj]
--     generalize_proofs _ _ h1 _ h3
--     apply h1.hom_ext
--     · simp only [IsPullback.lift_fst,((Topos.partialMapClassifier 𝒞 Z₂.left).isPullback _ _).w]
--     · simp [f.property]
--   right_inv := by
--     intro i_bar
--     ext
--     simp only [Functor.id_obj, Functor.const_obj_obj]
--     symm
--     generalize_proofs _ _ _ _ h1 h2 _
--     apply PartialMap.Classifier.uniq
--     apply IsPullback.of_bot _ (by simp) (PartialMap.Classifier.map_isPullback Z₂.hom
--       (Topos.partialMapClassifier 𝒞 _) (Topos.partialMapClassifier 𝒞 _))
--     simp only [Functor.const_obj_obj, Functor.id_obj, IsPullback.lift_snd]
--     rw [i_bar.property]
--     exact IsPullback.paste_vert (IsPullback.of_hasPullback _ _).flip
--       (PartialMap.Classifier.isPullback _ _ _)

-- lemma Over.exp.adjunction_equiv_2_apply_id {X : C} (Y Z : Over X) :
--   (adjunction_equiv_3 𝒞 Y Z (Y ⊗ Z)) (adjunction_equiv_2 Y Z (Y ⊗ Z)
-- ⟨𝟙 (Limits.pullback Y.hom Z.hom),sorry⟩) =
--     ⟨sorry,sorry⟩ := by
--   ext1

--   rw [adjunction_equiv_3_apply_coe,
--     adjunction_equiv_2_apply_coe]
--   simp
--   sorry

-- @[simps]
-- noncomputable def Over.exp.adjunction_equiv_4 {X : C} (Y : Over X) (Z₁ Z₂ : Over X) :
--     letI : Mono (CartesianMonoidalCategory.lift Y.hom (𝟙 Y.left)) :=
--       @mono_of_mono_fac _ _ _ _ _ _ _ _ (instMonoId _) (CartesianMonoidalCategory.lift_snd _ _)
--     { i_bar : Y.left ⊗ Z₁.left ⟶ (Topos.partialMapClassifier 𝒞 Z₂.left).obj //
--           i_bar ≫ (Topos.partialMapClassifier 𝒞 Z₂.left
--           ).map Z₂.hom (Topos.partialMapClassifier 𝒞 X) = Y.left ◁ Z₁.hom ≫ exp._θ _ _} ≃
--     { i : Z₁.left ⟶ (internalHom.obj (.op (Y.left))).obj
-- (Topos.partialMapClassifier 𝒞 Z₂.left).obj
--       // i ≫ (internalHom.obj (.op Y.left)).map
--         ((Topos.partialMapClassifier 𝒞 Z₂.left).map Z₂.hom (Topos.partialMapClassifier 𝒞 X)) =
--         Z₁.hom ≫ exp._θ_tilde 𝒞 Y } where
--   toFun i_bar := ⟨curry i_bar.val,by
--     apply uncurry_injective
--     rw [internalHom.obj_map, uncurry_natural_right,uncurry_curry,_θ_tilde,
--       uncurry_natural_left,uncurry_curry]
--     simpa using i_bar.property
--     ⟩
--   invFun i := ⟨uncurry i.val,by
--     apply curry_injective
--     rw [curry_natural_left,curry_natural_right,curry_uncurry,
--       ← _θ_tilde.eq_1,← internalHom.obj_map,i.property]⟩
--   left_inv := by intro; simp
--   right_inv := by intro; simp

-- @[simps]
-- noncomputable def Over.exp.adjunction_equiv_5 {X : C} (Y : Over X) (Z₁ Z₂ : Over X) :
--   { i : Z₁.left ⟶ (internalHom.obj (.op (Y.left))).obj (Topos.partialMapClassifier 𝒞 Z₂.left).obj
--       // i ≫ (internalHom.obj (.op Y.left)).map
--         ((Topos.partialMapClassifier 𝒞 Z₂.left).map Z₂.hom (Topos.partialMapClassifier 𝒞 X)) =
--         Z₁.hom ≫ exp._θ_tilde 𝒞 Y } ≃
--     ((Over.map (exp._θ_tilde 𝒞 Y)).obj Z₁ ⟶
--       Over.mk ((internalHom.obj (.op Y.left)).map
--         ((Topos.partialMapClassifier 𝒞 Z₂.left).map Z₂.hom
-- (Topos.partialMapClassifier 𝒞 X)))) where
--   toFun i := homMk (eqToHom (by simp) ≫ i.val) (by simp [i.property])
--   invFun i := ⟨i.left,by simpa using Over.w i ⟩
--   left_inv := by intro; simp
--   right_inv := by intro; simp

noncomputable def Over.exp.adjunctionUnit {X : C} (Y : Over X) :
    𝟭 (Over X) ⟶ (tensorLeft Y) ⋙ Over.exp 𝒞 Y where
  app Z := homMk (Limits.pullback.lift (curry ((
    @PartialMap.Classifier.χ _ _ _ _
      (Limits.pullback Y.hom Z.hom) _ (𝟙 _) (
        CartesianMonoidalCategory.lift (pullback.fst _ _) (pullback.snd _ _))
        (by
          constructor
          intro Z₂ g₁ g₂ h
          apply pullback.hom_ext
          · simpa using congr($h ≫ CartesianMonoidalCategory.fst _ _)
          · simpa using congr($h ≫ CartesianMonoidalCategory.snd _ _)))
    )) (Z.hom) (by
      simp only [Functor.id_obj, Functor.comp_obj, PartialMap.Classifier.mkFunctor_obj, _hom,
        forget_obj, Functor.comp_map, PartialMap.Classifier.mkFunctor_map, curriedTensor_obj_obj,
        lift_obj, tensorObj_left, Functor.const_obj_obj, tensorObj_hom, mk_left, mk_hom]
      apply uncurry_injective
      rw [internalHom.obj_map,uncurry_natural_right,_θ_tilde,uncurry_natural_left,
        uncurry_curry,uncurry_curry]
      simp only
      rw [PartialMap.Classifier.χ_comp_map,_θ]
      symm
      generalize_proofs h1 h2 h3
      refine @PartialMap.Classifier.uniq _ _ _ _ _ _ _ _ h3 _ ?_
      rw [Category.id_comp,]
      apply IsPullback.paste_vert (h₂₁ := CartesianMonoidalCategory.graph Y.hom)
      · apply IsPullback.of_right (by simpa using (IsPullback.of_hasPullback _ _).flip) _
          (IsPullback.whiskerLeft_horiz Z.hom _).flip
        ext <;> simp [pullback.condition]
      · exact PartialMap.Classifier.isPullback _ _ _)) (by simp [exp])
  naturality {Z₁ Z₂} f := (by
    ext
    simp only [Functor.id_obj, Functor.comp_obj, curriedTensor_obj_obj, Functor.id_map,
      PartialMap.Classifier.mkFunctor_obj, lift_obj, forget_obj, tensorObj_left,
      Functor.const_obj_obj, mk_left, mk_hom, comp_left, homMk_left, Functor.comp_map,
      curriedTensor_obj_map, exp, _hom]
    apply pullback.hom_ext
    · simp only [tensorObj_hom, Functor.id_obj, Functor.const_obj_obj,
      PartialMap.Classifier.mkFunctor_map, mk_left, mk_hom, pullback_obj_left, Category.assoc,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, lift_map, Functor.comp_obj,
      forget_obj, tensorObj_left, PartialMap.Classifier.mkFunctor_obj, Functor.comp_map, forget_map,
      pullback_map_left, homMk_left, limit.lift_π_assoc, cospan_left]
      apply uncurry_injective
      rw [uncurry_natural_left,uncurry_curry,
        internalHom.obj_map,uncurry_natural_right,uncurry_curry,
        PartialMap.Classifier.χ_comp_map]
      generalize_proofs _ h2 _ _ h5
      apply PartialMap.Classifier.uniq
      rw [Category.id_comp, whiskerLeft_left, ← Category.comp_id (pullback.map _ _ _ _ _ _ _ _ _)]
      apply IsPullback.paste_vert _ (PartialMap.Classifier.isPullback _ _ _)
      simp only [Functor.id_obj, Functor.const_obj_obj]
      apply IsPullback.of_right _ (by simp) (IsPullback.whiskerLeft_horiz _ _).flip
      simp only [CartesianMonoidalCategory.lift_snd]
      apply IsPullback.of_bot _ (by simp) (IsPullback.of_hasPullback _ _).flip
      simpa using (IsPullback.of_hasPullback _ _).flip
    · simp)

noncomputable def Over.exp.adjunctionCounit {X : C} (Y : Over X) :
    Over.exp 𝒞 Y ⋙ (tensorLeft Y) ⟶ 𝟭 (Over X) where
  app Z := homMk (
        let p : ((exp 𝒞 Y).obj Z).left ⟶ (MonoidalClosed.internalHom.obj (.op Y.left)).obj
          (Topos.partialMapClassifier 𝒞 Z.left).obj := pullback.fst _ _
        let q : ((exp 𝒞 Y).obj Z).left ⟶ X := ((exp 𝒞 Y).obj Z).hom
        have hpb : IsPullback p q ((MonoidalClosed.internalHom.obj (.op Y.left)).map _) _ :=
          IsPullback.of_hasPullback _ _
        have hpb2 := IsPullback.of_hasPullback Y.hom q
        have hpb3 : IsPullback (pullback.fst Y.hom q)
            (CartesianMonoidalCategory.lift (pullback.fst _ _) (pullback.snd _ _))
            (CartesianMonoidalCategory.graph Y.hom) (Y.left ◁ q) :=
          IsPullback.of_bot (by simpa using hpb2) (by ext <;> simp [pullback.condition])
            (IsPullback.whiskerLeft_horiz q Y.left)
        have hpb4 := hpb3.flip.paste_vert ((Topos.partialMapClassifier 𝒞 X).isPullback Y.hom
          (CartesianMonoidalCategory.graph Y.hom))
        have heq : Y.left ◁ q ≫ _θ 𝒞 Y = uncurry p ≫ (PartialMap.Classifier.mkFunctor (
            (Topos.partialMapClassifier 𝒞))).map Z.hom := by
          apply curry_injective
          rw [curry_natural_left,curry_natural_right,curry_uncurry,
            ← internalHom.obj_map,hpb.w, _θ_tilde,_θ]
        (PartialMap.Classifier.map_isPullback Z.hom
          (Topos.partialMapClassifier 𝒞 Z.left) (Topos.partialMapClassifier 𝒞 X)).lift
          (CartesianMonoidalCategory.lift (pullback.fst _ _) (pullback.snd _ _) ≫ uncurry p)
          (pullback.fst _ _ ≫ Y.hom) (by
            change IsPullback _ _ (_ ≫ _θ _ _) _ at hpb4
            simpa [heq] using hpb4.w))
  naturality {Z₁ Z₂} f := by
    ext
    simp only [Functor.comp_obj, curriedTensor_obj_obj, tensorObj_left, Functor.id_obj,
      Functor.const_obj_obj, Functor.comp_map, curriedTensor_obj_map,
      PartialMap.Classifier.mkFunctor_obj, lift_obj, forget_obj, mk_left, mk_hom, comp_left,
      homMk_left, Functor.id_map]
    generalize_proofs _ _ _ h4 _ h6 h7 _ h9
    apply h4.hom_ext
    · simp only [Category.assoc, IsPullback.lift_fst]
      rw [← ((Topos.partialMapClassifier 𝒞 Z₁.left).map_isPullback f.left _).w,
        whiskerLeft_left,CartesianMonoidalCategory.comp_lift_assoc,
        pullback.map,pullback.lift_fst,pullback.lift_snd,IsPullback.lift_fst_assoc,
        ← CartesianMonoidalCategory.lift_whiskerLeft_assoc,Category.comp_id,
        ← uncurry_natural_left,Category.assoc,← uncurry_natural_right]
      dsimp [exp]
      rw [pullback.lift_fst]
    · simp

noncomputable def Over.exp.adjunction {X : C} (Y : Over X) :
    tensorLeft Y ⊣ Over.exp 𝒞 Y where
  unit := Over.exp.adjunctionUnit 𝒞 Y
  counit := Over.exp.adjunctionCounit 𝒞 Y
  left_triangle_components Z := by
    ext
    simp only [Functor.id_obj, curriedTensor_obj_obj, tensorObj_left, Functor.const_obj_obj,
      Functor.comp_obj, exp.adjunctionUnit, PartialMap.Classifier.mkFunctor_obj, lift_obj,
      forget_obj, mk_left, mk_hom, curriedTensor_obj_map, exp.adjunctionCounit, tensorObj_hom,
      comp_left, whiskerLeft_left, pullback.map, Category.comp_id, homMk_left, IsPullback.comp_lift,
      CartesianMonoidalCategory.comp_lift_assoc, limit.lift_π, PullbackCone.mk_pt,
      PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_left, id_left]
    generalize_proofs h1 h2 h3 h4
    apply h2.hom_ext _ (by simp)
    simp only [IsPullback.lift_fst, Category.id_comp]
    rw [uncurry_eq,CartesianMonoidalCategory.lift_whiskerLeft_assoc,
      Category.assoc,pullback.lift_fst,← CartesianMonoidalCategory.lift_whiskerLeft_assoc,
      ← uncurry_eq,uncurry_curry]
    exact PartialMap.Classifier.χ_id_left _ _
  right_triangle_components Z := by
    ext
    simp only [exp, Functor.comp_obj, PartialMap.Classifier.mkFunctor_obj, _hom, forget_obj,
      Functor.comp_map, PartialMap.Classifier.mkFunctor_map, internalHom.obj_map, lift_obj,
      Functor.id_obj, pullback_obj_left, mk_left, mk_hom, curriedTensor_obj_obj, tensorObj_left,
      Functor.const_obj_obj, pullback_obj_hom, tensorObj_hom, adjunctionUnit, adjunctionCounit,
      lift_map, forget_map, homMk_left, comp_left, pullback_map_left, id_left]
    apply pullback.hom_ext _ (by simp)
    simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
    limit.lift_π_assoc, cospan_left, Category.id_comp]
    rw [← curry_natural_right, curry_eq_iff, PartialMap.Classifier.χ_comp_map,
      Category.id_comp]
    symm
    apply PartialMap.Classifier.uniq _ _ _ (hm := _) _
    generalize_proofs h1 h2 h3 h4
    apply IsPullback.of_bot _ (by simp) h3
    simp only [IsPullback.lift_snd]
    rw [← uncurry_natural_right,pullback.condition,pullback.condition]
    dsimp [_θ_tilde]
    rw [uncurry_natural_left,uncurry_curry, ← pullback.condition]
    apply IsPullback.paste_vert _ (PartialMap.Classifier.isPullback _ Y.hom
      (CartesianMonoidalCategory.graph Y.hom))
    apply IsPullback.of_right _ _ (IsPullback.whiskerLeft_horiz _ _).flip
    · simpa using (IsPullback.of_hasPullback _ _).flip
    · ext <;> simp [pullback.condition]

noncomputable def Over.closed {X : C} (Y : Over X) : Closed Y where
  rightAdj := Over.exp 𝒞 Y
  adj := Over.exp.adjunction 𝒞 Y

/-- Topoi are locally cartesian closed -/
noncomputable instance [HasClassifier C] {X : C} : MonoidalClosed (Over X) where
  closed Y := Over.closed ‹HasClassifier C›.exists_classifier.some Y

section

variable [HasClassifier C] (X : C)

/-
The Fundamental Theorem of Topos Theory:
Over categories of a topos are topoi
-/
#synth HasClassifier (Over X)
#synth HasFiniteLimits (Over X)
#synth MonoidalClosed (Over X)

end

end

end CategoryTheory
