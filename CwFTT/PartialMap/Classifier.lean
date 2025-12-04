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

noncomputable def PartialMap.Classifier.represents [HasPullbacks C] {Y : C} (Y' : PartialMap.Classifier Y) :
    (partialMapsTo Y).RepresentableBy (Y'.obj) where
  homEquiv := fun {X} => by
    change (X ⟶ Y'.obj) ≃ X⇀Y
    refine {
      toFun f := ThinSkeleton.mk ({
        obj := BinaryFan.mk (pullback.fst f Y'.η) (pullback.snd f Y'.η)
        property := IsPullback.mono_fst (.of_hasPullback _ _)
      })
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
        simp only [Functor.const_obj_obj, ThinSkeleton.mk, Quotient.mk', Quotient.lift_mk,
          BinaryFan.mk_pt, BinaryFan.mk_snd, BinaryFan.mk_fst]
        symm
        apply Y'.uniq
        exact IsPullback.of_hasPullback _ _
      right_inv := by
        intro f
        simp
        induction f with
        | h_mk m f =>
          dsimp [PartialMap.mk,ThinSkeleton.mk,Quotient.mk']
          change PartialMap.mk _ _ = PartialMap.mk _ _
          rw [PartialMap.mk_eq]
          use (Y'.isPullback f m).isoPullback.symm
          simp
    }
  homEquiv_comp := fun {X X'} f g => by
    simp only [partialMapsTo_obj, Functor.const_obj_obj, _root_.id_eq, partialMapsTo_map,
      Functor.op_obj, Quiver.Hom.unop_op]
    dsimp [(· ≫ ·)]
    apply Quotient.sound
    constructor
    simp only [Bicategory.precomposing_obj, Bicategory.precomp_obj]
    refine (ObjectProperty.IsPartialMap X Y).isoMk ?_
    simp [PrePartialMap.mkOfHom,PrePartialMap.mk, (· ≫ ·), PrePartialMap.comp]
    fapply BinaryFan.ext (pullbackRightPullbackFstIso g Y'.η f).symm <;> simp

def PartialMap.Classifier.ofRepresents [HasPullbacks C] {Y Y': C}
    (hY' : (partialMapsTo Y).RepresentableBy Y') : PartialMap.Classifier Y where
  obj := Y'
  η := hY'.homEquiv.symm (ofHom (𝟙 Y))
  isMono.right_cancellation {Z} f g h := by
    have := congr(hY'.homEquiv $h)
    simp_rw [hY'.homEquiv_comp] at this
    simp only [partialMapsTo_obj, Functor.op_obj, withPartialMaps_obj_out, partialMapsTo_map,
      Quiver.Hom.unop_op] at this

    sorry

  χ f m _ := _
  isPullback := _
  uniq := _

end CategoryTheory
