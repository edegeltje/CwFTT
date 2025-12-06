import CwFTT.PartialMap.Def

universe u v
namespace CategoryTheory
open Limits

variable {C : Type u} [Category.{v} C]
-- variable (C) in

/-- An a classifier of partial maps into `Y` consists of an object `Y'`
  and a mono `η : Y ⟶ Y'`, such that
  for every partial map (f : X ⇀ Y), there is a unique map
    (X ⟶ Y') making the partial map the pullback of this map along `η`. -/
protected structure PartialMap.Classifier (Y : C) where
  obj : C
  η : Y ⟶ obj
  [isMono : Mono η]
  χ {U X : C} (f : U ⟶ Y) (m : U ⟶ X) [Mono m] : X ⟶ obj
  isPullback {U X : C} (f : U ⟶ Y) (m : U ⟶ X) [Mono m] : IsPullback m f (χ f m) η
  uniq {U X : C} {f : U ⟶ Y} {m : U ⟶ X} [Mono m] {χ' : X ⟶ obj}
    (h : IsPullback m f χ' η) : χ' = χ f m

attribute [instance] PartialMap.Classifier.isMono

noncomputable def PartialMap.Classifier.represents [HasPullbacks C] {Y : C}
    (Y' : PartialMap.Classifier Y) : (partialMapsTo Y).RepresentableBy (Y'.obj) where
  homEquiv := fun {X} => by
    change (X ⟶ Y'.obj) ≃ X ⇀ Y
    refine {
      toFun f := PartialMap.mk (pullback.fst f Y'.η) (pullback.snd f Y'.η)
      invFun := Quotient.lift (fun f => Y'.χ f.obj.snd f.obj.fst) (by
        intro f f' hf
        simp only [Functor.const_obj_obj]
        have := Classical.choice hf
        let Z := (ObjectProperty.ι (.IsPartialMap _ _) ⋙ Cones.forget (pair _ _)).mapIso this
        apply Y'.uniq
        fapply IsPullback.of_iso (Y'.isPullback f.obj.snd f.obj.fst)
          ((ObjectProperty.ι (.IsPartialMap _ _) ⋙ Cones.forget (pair _ _)).mapIso
            (Classical.choice hf)) (Iso.refl _) (Iso.refl _) (Iso.refl _) <;> simp
        )
      left_inv := by
        intro f_tilde
        symm
        apply Y'.uniq
        exact IsPullback.of_hasPullback _ _
      right_inv := by
        intro f
        induction f with
        | h_mk m f =>
          dsimp
          rw [PartialMap.mk_eq]
          use (Y'.isPullback f m).isoPullback.symm
          simp [PartialMap.mk, Quotient.mk']
    }
  homEquiv_comp := fun {X X'} f g => by
    dsimp
    rw [PartialMap.ofHom_eq_mk, mk_comp_mk_of_isPullback _ _ _ _ (.of_hasPullback _ _)]
    simp only [Category.comp_id, PartialMap.mk_eq]
    use (pullbackRightPullbackFstIso _ _ _).symm
    simp

lemma PartialMap.Classifier.ofRepresents_isMono [HasPullbacks C] {Y Y' : C}
    (hY' : (partialMapsTo Y).RepresentableBy Y') : Mono (hY'.homEquiv.symm (ofHom (𝟙 Y))) where
  right_cancellation {Z} f g h := by
    have := congr(hY'.homEquiv $h)
    simp_rw [hY'.homEquiv_comp] at this
    simp only [partialMapsTo_obj, WithPartialMaps.toLocallyDiscrete_obj_as, partialMapsTo_map,
      Functor.comp_obj, StrictPseudofunctor.toFunctor_obj, withPartialMaps_obj,
      Quiver.Hom.unop_op] at this
    have : ofHom f ≫ ofHom (𝟙 Y) = ofHom g ≫ ofHom (𝟙 Y) := by
      convert this <;> exact (hY'.homEquiv.apply_symm_apply (ofHom (𝟙 Y))).symm
    simp only [ofHom_comp_ofHom, Category.comp_id] at this
    exact WithPartialMaps.ofHom_injective this

lemma PartialMap.Classifier.ofRepresents_isPullback [HasPullbacks C] {Y Y': C}
    (hY' : (partialMapsTo Y).RepresentableBy Y') {U X : C} (f : U ⟶ Y) (m : U ⟶ X) [Mono m] :
    IsPullback m f (hY'.homEquiv.symm (PartialMap.mk m f)) (hY'.homEquiv.symm (ofHom (𝟙 Y))) := by
    refine ⟨⟨by
      simp_rw [hY'.comp_homEquiv_symm]
      congr 1
      simp only [partialMapsTo_obj, WithPartialMaps.toLocallyDiscrete_obj_as, partialMapsTo_map,
        Functor.comp_obj, StrictPseudofunctor.toFunctor_obj, withPartialMaps_obj,
        Quiver.Hom.unop_op, ofHom_comp_ofHom, Category.comp_id]
      rw [PartialMap.ofHom_eq_mk,
        PartialMap.mk_comp_mk_of_isPullback _ _ _ _ (IsPullback.of_horiz_isIso_mono
          (fst := (𝟙 _)) (snd := (𝟙 _)) (by simp))]
      simp [PartialMap.ofHom_eq_mk]⟩,⟨?_⟩⟩
    fapply PullbackCone.IsLimit.mk
    · intro s
      have : ∃ e : _ ≅ s.pt, e.hom ≫ 𝟙 s.pt = pullback.fst s.fst m ≫ 𝟙 s.pt ∧
          e.hom ≫ s.snd = pullback.snd s.fst m ≫ f := by
        rw [← mk_eq, ← mk_comp_mk_of_isPullback _ _ _ _ (.of_hasPullback _ _),
          ← ofHom_eq_mk,← ofHom_eq_mk]
        have := s.condition
        simp_rw [hY'.comp_homEquiv_symm] at this
        simpa using hY'.homEquiv.symm.injective this
      exact this.choose.symm.hom ≫ (pullback.snd _ _)
    · intro s
      simp only [partialMapsTo_obj, WithPartialMaps.toLocallyDiscrete_obj_as, Category.comp_id,
        Iso.symm_hom, Category.assoc]
      generalize_proofs h₁ he
      obtain ⟨he₁,he₂⟩ := he.choose_spec
      rw [Iso.inv_comp_eq,he₁,pullback.condition]
    · intro s
      simp only [partialMapsTo_obj, WithPartialMaps.toLocallyDiscrete_obj_as, Category.comp_id,
        Iso.symm_hom, Category.assoc]
      generalize_proofs hpb he
      obtain ⟨he₁,he₂⟩ := he.choose_spec
      rw [Iso.inv_comp_eq, he₂]
    · intro s m' hm₁ hm₂
      simp only [partialMapsTo_obj, WithPartialMaps.toLocallyDiscrete_obj_as, Category.comp_id,
        Iso.symm_hom]
      generalize_proofs hpb he
      rw [Iso.eq_inv_comp, ← cancel_mono m,Category.assoc,hm₁,
        he.choose_spec.left, pullback.condition]

def PartialMap.Classifier.ofRepresents [HasPullbacks C] {Y Y': C}
    (hY' : (partialMapsTo Y).RepresentableBy Y') : PartialMap.Classifier Y where
  obj := Y'
  η := hY'.homEquiv.symm (ofHom (𝟙 Y))
  isMono := ofRepresents_isMono hY'
  χ {U X} f m _ := hY'.homEquiv.symm (PartialMap.mk m f)
  isPullback {U X} f m _ := ofRepresents_isPullback hY' f m
  uniq {U X f m} _ χ' hχ' := by
    rw [← Equiv.apply_eq_iff_eq_symm_apply]
    have := ofRepresents_isMono hY'
    have hfm := ofRepresents_isPullback hY' f m
    have h1 : m ≫ χ' = m ≫ (hY'.homEquiv.symm (.mk m f)) := by
      rw [hχ'.w,hfm.w]
    have h2 : hY'.homEquiv.symm (.mk m f) = hY'.homEquiv.symm (.mk m f ≫ ofHom (𝟙 Y)) := by
      simp only [partialMapsTo_obj, WithPartialMaps.toLocallyDiscrete_obj_as, Functor.op_obj,
        Functor.comp_obj, StrictPseudofunctor.toFunctor_obj, withPartialMaps_obj, mk_comp_ofHom,
        Category.comp_id]


    -- rw [← Equiv.apply_eq_iff_eq_symm_apply]
    -- rw [← Category.comp_id χ',hY'.homEquiv_comp]
    -- simp only [partialMapsTo_obj, partialMapsTo_map, Functor.comp_obj,
    --   StrictPseudofunctor.toFunctor_obj, withPartialMaps_obj,
    --   WithPartialMaps.toLocallyDiscrete_obj_as, Quiver.Hom.unop_op]
    -- have : (hY'.homEquiv (ofHom (𝟙 Y'))) = hY'.homEquiv.symm (ofHom (𝟙 Y)) := by
    -- --   sorry
    sorry

end CategoryTheory
