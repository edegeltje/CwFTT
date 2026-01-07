import CwFTT.PartialMap.Def
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Topos.Classifier

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
  uniq {U X : C} (f : U ⟶ Y) (m : U ⟶ X) [hm : Mono m] {χ' : X ⟶ obj}
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


instance PartialMap.Classifier.ofRepresents_isMono [HasPullbacks C] {Y Y' : C}
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

lemma PartialMap.Classifier.ofRepresents_isPullback [HasPullbacks C] {Y Y' : C}
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

lemma PartialMap.Classifier.ofRepresents_homEquiv_id [HasPullbacks C] {Y Y' : C}
    (hY' : (partialMapsTo Y).RepresentableBy Y') :
    hY'.homEquiv (𝟙 Y') = PartialMap.mk (hY'.homEquiv.symm (ofHom (𝟙 Y))) (𝟙 Y) := by
  induction h:hY'.homEquiv (𝟙 Y') using PartialMap.induction with
  | h_mk m f =>
    rename_i U _
    dsimp at m f
    have := ofRepresents_isPullback hY' f m
    rw [← h] at this
    simp only [partialMapsTo_obj, Equiv.symm_apply_apply,
      WithPartialMaps.toLocallyDiscrete_obj_as] at this
    rw [PartialMap.mk_eq]
    use this.isoIsPullback _ _ (IsPullback.of_id_snd)
    simp [-Category.comp_id]

def PartialMap.Classifier.ofRepresents [HasPullbacks C] {Y Y' : C}
    (hY' : (partialMapsTo Y).RepresentableBy Y') : PartialMap.Classifier Y where
  obj := Y'
  η := hY'.homEquiv.symm (ofHom (𝟙 Y))
  isMono := ofRepresents_isMono hY'
  χ {U X} f m _ := hY'.homEquiv.symm (PartialMap.mk m f)
  isPullback {U X} f m _ := ofRepresents_isPullback hY' f m
  uniq {U X f m} _ χ' hχ' := by
    have hfm := ofRepresents_isPullback hY' f m
    rw [← Equiv.apply_eq_iff_eq_symm_apply, hY'.homEquiv_eq, ofRepresents_homEquiv_id hY']
    simp only [partialMapsTo_obj, WithPartialMaps.toLocallyDiscrete_obj_as, partialMapsTo_map,
      Functor.comp_obj, StrictPseudofunctor.toFunctor_obj, withPartialMaps_obj, Quiver.Hom.unop_op]
    have := hχ'.mono_fst
    simp_rw [ofHom_eq_mk]
    apply Eq.trans (mk_comp_mk_of_isPullback (𝟙 _) χ' (hY'.homEquiv.symm (ofHom (𝟙 Y))) (𝟙 _) hχ')
    simp

lemma PartialMap.Classifier.ofRepresents_represents [HasPullbacks C] {Y : C}
    (Y' : PartialMap.Classifier Y) : ofRepresents (Y'.represents) = Y' := by
  cases Y' with
  | mk obj η χ isPullback uniq =>
    dsimp [ofRepresents,represents]
    congr
    change χ (𝟙 Y) (𝟙 Y) = _
    symm
    apply uniq
    rw [← mono_iff_isPullback]
    assumption

open PrePartialMap in
def PartialMapsToTerminalIso [HasPullbacks C] (Ω₀ : C) (hΩ₀ : IsTerminal Ω₀) :
    (partialMapsTo Ω₀) ≅ (Subobject.presheaf C) :=
  NatIso.ofComponents (
    fun X => {
      hom := PartialMap.support.obj
      inv := (ThinSkeleton.map (C := MonoOver X.unop) (D := (X.unop ⇀' Ω₀))
        {
          obj s := @PrePartialMap.mk C _ _ _ _ _ s.property (hΩ₀.from _)
          map {s₁ s₂} f := PrePartialMap.homMk f.hom.left (Over.w _) (by simp)
        }).obj
      hom_inv_id := by
        dsimp [PartialMap.support]
        ext t
        induction t using PartialMap.induction with
        | h_mk m f =>
          rename_i U _
          simp only [PartialMap.mk, ThinSkeleton.mk, Quotient.mk', types_comp_apply,
            ThinSkeleton.map_obj, Quotient.map_mk, types_id_apply]
          change PartialMap.mk _ _ = .mk _ _
          rw [PartialMap.mk_eq]
          simp only [overMono, Functor.const_obj_obj, mk_obj_pt, mk_obj_fst, Over.mk_left,
            Over.mk_hom]
          use Iso.refl _
          simpa using hΩ₀.hom_ext _ _
      inv_hom_id := by
        dsimp [PartialMap.support]
        ext1 x
        induction x using Subobject.ind with
        | h f =>
          rfl
    }
  ) (fun {X Y} f => by
    ext g
    induction g using PartialMap.induction with
    | h_mk m' f' =>
      rename_i U _
      dsimp [-ThinSkeleton.map_obj,PartialMap.support]
      rw [PartialMap.ofHom_eq_mk,PartialMap.mk_comp_mk_of_isPullback _ _ _ _ (.of_hasPullback _ _)]
      -- rw [PartialMap.mk]
      simp only [PartialMap.mk, ThinSkeleton.mk, Quotient.mk', Category.comp_id,
        ThinSkeleton.map_obj, Quotient.map_mk]
      change Subobject.mk _ = (Subobject.pullback f.unop).obj (Subobject.mk _)
      rw [Subobject.pullback_obj]
      trans Subobject.mk (pullback.snd m' f.unop)
      · refine Subobject.mk_eq_mk_of_comm (pullback.fst f.unop m') (pullback.snd m' f.unop) ?_ ?_
        · exact pullbackSymmetry f.unop m'
        · simp
      · have hm' := IsPullback.of_hasPullback m' f.unop
        have := IsPullback.of_hasPullback (Subobject.mk m').arrow f.unop
        have := this.of_iso
          (fst' := pullback.fst _ _ ≫ (Subobject.underlyingIso m').hom)
          (snd' := pullback.snd _ _) (f' := m') (g' := f.unop) (Iso.refl _)
          (Subobject.underlyingIso m') (Iso.refl _) (Iso.refl _)
          (by simp) (by simp) (by simp) (by simp)
        refine Subobject.mk_eq_mk_of_comm (pullback.snd m' f.unop)
          (pullback.snd (Subobject.mk m').arrow f.unop) (hm'.isoIsPullback _ _ this) ?_
        simp
  )

/--
A subobject classifier is in particular a classifier of partial maps into the terminal object.
-/
@[simps!]
noncomputable def Classifier.toPartialMapClassifier [HasPullbacks C] (𝒞 : Classifier C) :
    PartialMap.Classifier (𝒞.Ω₀) :=
  .ofRepresents (𝒞.representableBy.ofIso (PartialMapsToTerminalIso _ 𝒞.isTerminalΩ₀).symm)

/--
A partial map classifier for a terminal object classifies subobjects.
-/
@[simps!]
noncomputable def PartialMap.Classifier.toClassifier [HasPullbacks C] {Ω₀ : C} (hΩ₀ : IsTerminal Ω₀)
    (𝒞 : PartialMap.Classifier Ω₀) : Classifier C :=
  letI : HasTerminal C := hΩ₀.hasTerminal
  Classifier.SubobjectRepresentableBy.classifier
    (𝒞.represents.ofIso (PartialMapsToTerminalIso _ hΩ₀))


def PartialMap.Classifier.map {X Y : C} (f : X ⟶ Y) (𝒳 : PartialMap.Classifier X)
    (𝒴 : PartialMap.Classifier Y) : 𝒳.obj ⟶ 𝒴.obj := 𝒴.χ f 𝒳.η

lemma PartialMap.Classifier.map_isPullback {X Y : C} (f : X ⟶ Y)
    (𝒳 : PartialMap.Classifier X) (𝒴 : PartialMap.Classifier Y) :
    IsPullback (𝒳.η) f (𝒳.map f 𝒴) 𝒴.η :=
  𝒴.isPullback _ _

lemma PartialMap.Classifier.χ_comp_map {X Y : C} (f : X ⟶ Y)
    (𝒳 : PartialMap.Classifier X) (𝒴 : PartialMap.Classifier Y)
    {U V : C} (m : U ⟶ V) [Mono m] (g : U ⟶ X) :
    𝒳.χ g m ≫ 𝒳.map f 𝒴 = 𝒴.χ (g ≫ f) m := by
  apply 𝒴.uniq
  apply IsPullback.paste_vert
  · exact 𝒳.isPullback _ _
  · exact map_isPullback _ _ _

lemma PartialMap.Classifier.map_comp {X Y Z : C}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (𝒳 : PartialMap.Classifier X) (𝒴 : PartialMap.Classifier Y)
    (𝒵 : PartialMap.Classifier Z) :
    𝒳.map (f ≫ g) 𝒵 = 𝒳.map f 𝒴 ≫ 𝒴.map g 𝒵 := by
  symm
  apply 𝒵.uniq
  apply IsPullback.paste_vert
  · exact map_isPullback _ _ _
  · exact map_isPullback _ _ _

lemma PartialMap.Classifier.map_id {X : C}
    (𝒳 : PartialMap.Classifier X) : 𝒳.map (𝟙 X) 𝒳 = 𝟙 𝒳.obj := by
  symm
  apply 𝒳.uniq
  apply IsPullback.id_vert

@[simps obj map]
def PartialMap.Classifier.mkFunctor (obj : ∀ X:C, PartialMap.Classifier X) :
    C ⥤ C where
  obj X := (obj X).obj
  map {X Y} f := (obj X).map f (obj Y)
  map_id X := (obj X).map_id
  map_comp {X Y Z} f g := (obj X).map_comp f g (obj Y) (obj Z)


def PartialMap.Classifier.hom_ext {X Y : C} (𝒳 : PartialMap.Classifier X)
  (g₁ g₂ : Y ⟶ 𝒳.obj) {U : C} (m : U ⟶ Y) [hm : Mono m] (f : U ⟶ X)
  (hg₁ : IsPullback m f g₁ 𝒳.η) (hg₂ : IsPullback m f g₂ 𝒳.η) : g₁ = g₂ := by
  trans 𝒳.χ f m
  · exact 𝒳.uniq _ _ hg₁
  · symm
    exact 𝒳.uniq _ _ hg₂

lemma PartialMap.Classifier.χ_id_right {X Y : C} (f : X ⟶ Y) (𝒴 : PartialMap.Classifier Y) :
    𝒴.χ f (𝟙 X) = f ≫ 𝒴.η := by
  simpa using (𝒴.isPullback f (𝟙 X)).w

lemma PartialMap.Classifier.χ_id_left {X Y : C} (m : X ⟶ Y) [Mono m] (𝒳 : PartialMap.Classifier X) :
    m ≫ 𝒳.χ (𝟙 _) m = 𝒳.η := by
  simpa using (((mono_iff_isPullback m).mp ‹Mono m›).paste_vert (𝒳.isPullback (𝟙 _) m)).w

end CategoryTheory
