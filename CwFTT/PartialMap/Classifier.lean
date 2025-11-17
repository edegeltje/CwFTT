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
  Y' : C
  η : Y ⟶ Y'
  [isMono : Mono η]
  χ {U X : C} (f : U ⟶ Y) (m : U ⟶ X) [Mono m] : X ⟶ Y'
  isPullback {U X : C} (f : U ⟶ Y) (m : U ⟶ X) [Mono m] : IsPullback m f (χ f m) η
  uniq {U X : C} {f : U ⟶ Y} {m : U ⟶ X} [Mono m] {χ' : X ⟶ Y'}
    (h : IsPullback m f χ' η) : χ' = χ f m

attribute [instance] PartialMap.Classifier.isMono

def PartialMap.Classifier.represents [HasPullbacks C] {Y : C} (Y' : PartialMap.Classifier Y) :
    (partialMaps.flip.obj Y ⋙ forget _).RepresentableBy (Y'.Y') where
  homEquiv := fun {X} => by
    change (X ⟶ Y'.Y') ≃ X⇀Y
    refine {
      toFun f := ThinSkeleton.mk ({
        obj := BinaryFan.mk (pullback.fst f Y'.η) (pullback.snd f Y'.η)
        property := IsPullback.mono_fst (.of_hasPullback _ _)
      })
      invFun := _
      left_inv := _
      right_inv := _
    }
  homEquiv_comp := fun {X X'} f g => by
    simp [partialMaps]



end CategoryTheory
