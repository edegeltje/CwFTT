import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
given a strict bicategory B, we get a functor `Bᵒᵖ ⥤ B ⥤ Cat`
-/

universe w w₂ v v₂ u u₂
namespace CategoryTheory
namespace Bicategory
variable (B : Type u) [Bicategory.{w, v} B]

section
def coyoneda [Bicategory.Strict B] : Bᵒᵖ ⥤ B ⥤ Cat where
  obj X := {
    obj Y := .mk <| X.unop ⟶ Y
    map {Y₁ Y₂} f := postcomp X.unop f
    map_id Y := Functor.ext (by simp) (by simp [Strict.rightUnitor_eqToIso])
    map_comp {Y₁ Y₂ Y₃} f g := Functor.ext (by simp) (by simp [Strict.associator_eqToIso])
  }
  map {X₁ X₂} f := {
    app Y := precomp Y f.unop
    naturality {Y₁ Y₂} g := Functor.ext (by simp) (by simp [Strict.associator_eqToIso])
  }
  map_id X := by
    ext Y
    apply Functor.ext (by simp) (by simp [Strict.leftUnitor_eqToIso])
  map_comp {X₁ X₂ X₃} f g := by
    ext Y
    apply Functor.ext (by simp) (by simp [Strict.associator_eqToIso])
end

section PseudoNatTrans
variable (B₂ : Type u₂) [Bicategory.{w₂, v₂} B₂] (F G : B ⥤ᵖ B₂)
variable {B B₂}

structure PseudoNatTrans where
  app (X : B) : F.obj X ⟶ G.obj X
  app₂ {X Y : B} (f : X ⟶ Y) : (F.map f ≫ app Y) ≅ (app X ≫ G.map f)
  app₂_naturality {X Y : B} {f g : X ⟶ Y} (h : f ⟶ g) :
    (F.map₂ h) ▷ app Y ≫ (app₂ g).hom = (app₂ f).hom ≫ app X ◁ (G.map₂ h) := by cat_disch
  unitality (X : B) :
    (rightUnitor (app X)).hom ≫ (leftUnitor (app X)).inv ≫ (F.mapId _).inv ▷ app X =
    app X ◁ (G.mapId X).inv ≫ (app₂ (𝟙 X)).inv := by cat_disch
  associativity {X₁ X₂ X₃ : B} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) :
    ((app₂ f).inv ▷ (G.map g)) ≫ (associator _ _ _).hom ≫ (F.map f ◁ (app₂ g).inv) ≫
      (associator _ _ _).inv ≫ (F.mapComp f g).inv ▷ _ =
    (associator _ _ _).hom ≫ _ ◁ (G.mapComp f g).inv ≫
      (app₂ (f ≫ g)).inv := by cat_disch

instance : Quiver (B ⥤ᵖ B₂) where
  Hom {F G} := PseudoNatTrans F G

variable {F G}

variable (α β : F ⟶ G)

structure PseudoModification where
  mod (X : B) : α.app X ⟶ β.app X
  mod_naturality {X Y : B} (f : X ⟶ Y) :
    mod X ▷ G.map f ≫ (β.app₂ f).inv = (α.app₂ f).inv ≫ (F.map f ◁ (mod Y)) := by
    cat_disch

variable {α β}

namespace PseudoModification

instance : Quiver (F ⟶ G) where
  Hom {α β} := PseudoModification α β

@[ext]
lemma ext (a b : α ⟶ β) (h : ∀ X, a.mod X = b.mod X) : a = b := by
  cases a ; cases b; congr; ext ; simp_all

def comp {γ : F ⟶ G} (a : α ⟶ β) (b : β ⟶ γ) : α ⟶ γ where
  mod X := a.mod X ≫ b.mod X
  mod_naturality {X Y : B} f := by
    rw [comp_whiskerRight_assoc,b.mod_naturality,
      reassoc_of% a.mod_naturality,whiskerLeft_comp]

lemma assoc {γ δ : F ⟶ G} (a : α ⟶ β) (b : β ⟶ γ) (c : γ ⟶ δ) :
    comp (comp a b) c = comp a (comp b c) := by
  ext X ; simp [comp]

variable (α) in
def id : α ⟶ α where
  mod X := (𝟙 (α.app X))

lemma comp_id (a : α ⟶ β) : a.comp (.id β) = a := by
  ext X; simp [id,comp]

lemma id_comp (a : α ⟶ β) : comp (id α) a = a := by
  ext X; simp [id,comp]

instance : Category (F ⟶ G) where
  id X := id X
  comp f g := comp f g
  id_comp := id_comp
  comp_id := comp_id
  assoc := assoc

variable (α) in
@[simp]
lemma id_mod_app (X : B) : PseudoModification.mod (𝟙 α) X = 𝟙 (α.app X) := rfl

@[simp]
lemma comp_mod_app {γ : F ⟶ G} (a : α ⟶ β) (b : β ⟶ γ) (X : B) :
    (a ≫ b).mod X = a.mod X ≫ b.mod X := rfl

end PseudoModification

namespace PseudoNatTrans

@[simps]
def ext {α β : F ⟶ G} (appIso : ∀ X, α.app X ≅ β.app X)
    (happIso_nat : ∀ {X Y : B} (f : X ⟶ Y), (appIso X).hom ▷ G.map f ≫ (β.app₂ f).inv =
      (α.app₂ f).inv ≫ F.map f ◁ (appIso Y).hom) :
    α ≅ β where
  hom := {
    mod X := (appIso X).hom
    mod_naturality {X Y} f := happIso_nat f
  }
  inv := {
    mod X := (appIso X).inv
    mod_naturality {X Y} f := by
      rw [← whiskerRightIso_inv, ← whiskerLeftIso_inv, Iso.eq_comp_inv, Category.assoc,
        Iso.inv_comp_eq, whiskerLeftIso_hom,← happIso_nat, whiskerRightIso_hom]
  }
  hom_inv_id := by ext X; simp
  inv_hom_id := by ext X; simp

@[reassoc]
def associativity_symm (α : F ⟶ G) {X₁ X₂ X₃} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) :
    (α.app X₁) ◁ (G.mapComp f g).inv ≫ (α.app₂ (f ≫ g)).inv =
    (α_ _ _ _).inv ≫ ((α.app₂ f).inv ▷ (G.map g)) ≫ (α_ _ _ _).hom ≫
    (F.map f ◁ (α.app₂ g).inv) ≫ (α_ _ _ _).inv ≫ (F.mapComp f g).inv ▷ _ := by
  simp [associativity]

@[simps]
def comp {H : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) : F ⟶ H where
  app X := α.app X ≫ β.app X
  app₂ {X Y} f := (associator _ _ _).symm ≪≫ whiskerRightIso (α.app₂ _) (β.app Y) ≪≫
    ((associator _ _ _) ≪≫ whiskerLeftIso _ (β.app₂ _) ≪≫ (associator _ _ _).symm)
  app₂_naturality {X Y} {f g} h := by
    simp only [whiskerRight_comp, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
      whiskerLeftIso_hom, Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerLeft,
      Iso.inv_hom_id_assoc, Iso.cancel_iso_inv_left]
    rw [← comp_whiskerRight_assoc, α.app₂_naturality,comp_whiskerRight,whisker_assoc,
      Category.assoc,Category.assoc,Category.assoc,
      Iso.inv_hom_id_assoc,← whiskerLeft_comp_assoc,β.app₂_naturality,
        whiskerLeft_comp_assoc]
  unitality X := by
    simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv,
      Category.assoc, whiskerRightIso_inv]
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, ← β.unitality]
    simp only [whiskerRight_comp, whiskerLeft_comp, whiskerLeft_rightUnitor, Category.assoc,
      Iso.hom_inv_id_assoc, Iso.cancel_iso_hom_left]
    rw [@associator_inv_naturality_middle_assoc,
      ← comp_whiskerRight_assoc, ← α.unitality]
    simp
  associativity {X₁ X₂ X₃} f g := by
    simp only [Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, Category.assoc, whiskerRightIso_inv]
    rw [comp_whiskerLeft_assoc, Iso.inv_hom_id_assoc]
    simp only [comp_whiskerRight, whisker_assoc, Category.assoc, whiskerLeft_comp,
      whiskerRight_comp, pentagon_hom_inv_inv_inv_inv_assoc, pentagon_assoc]
    rw [← whiskerLeft_comp_assoc (α.app X₁), β.associativity_symm]
    simp only [whiskerLeft_comp, Category.assoc, pentagon_hom_hom_inv_hom_hom_assoc]
    rw [whisker_assoc_symm_assoc (α.app X₁) (G.mapComp f g).inv (β.app X₃),
      Iso.hom_inv_id_assoc,← comp_whiskerRight_assoc _ ((α.app₂ (f ≫ g)).inv) (β.app X₃),
      α.associativity_symm]
    simp only [comp_whiskerRight, whisker_assoc, Category.assoc, pentagon_inv_assoc]
    simp_rw [associator_naturality_left_assoc, associator_inv_naturality_right_assoc,
      pentagon_inv_inv_hom_hom_inv_assoc]
    simp only [← Category.assoc]
    congr 4
    simp only [Category.assoc]
    congr 3
    rw [← pentagon_hom_hom_inv_hom_hom_assoc, associator_naturality_left_assoc,
      Iso.inv_hom_id_assoc, whisker_exchange_assoc]
    simp

variable (F) in
@[simps]
def id : F ⟶ F where
  app X := 𝟙 _
  app₂ {X Y} f := (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm

@[simps]
def whiskerLeft {H : B ⥤ᵖ B₂} (γ : H ⟶ F) (a : α ⟶ β) : comp γ α ⟶ comp γ β where
  mod X := γ.app X ◁ a.mod X
  mod_naturality {X Y} f := by
    simp only [comp_app, whisker_assoc, comp_app₂, Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv,
      Category.assoc, whiskerRightIso_inv, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
    rw [← whiskerLeft_comp_assoc,a.mod_naturality]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [@associator_inv_naturality_right_assoc,whisker_exchange_assoc]
    simp

@[simps]
def whiskerRight {H : B ⥤ᵖ B₂} (a : α ⟶ β) (γ : G ⟶ H) : comp α γ ⟶ comp β γ where
  mod X := a.mod X ▷ γ.app X
  mod_naturality {X Y} f := by
    simp only [comp_app, comp_app₂, Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, Category.assoc,
      whiskerRightIso_inv]
    rw [@associator_naturality_left_assoc,← whisker_exchange_assoc]
    simp only [whiskerRight_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_hom_left]
    rw [← comp_whiskerRight_assoc,a.mod_naturality]
    simp

-- variable (α β) in
@[simps!]
def associator {F G H I : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ I) :
    comp (comp α β) γ ≅ comp α (comp β γ) :=
  ext (fun X => α_ (α.app X) (β.app X) (γ.app X)) (by simp)

variable (α) in
@[simps!]
def leftUnitor : comp (id F) α ≅ α :=
  ext (fun X => λ_ (α.app X)) (by simp)

variable (α) in
@[simps!]
def rightUnitor : comp α (id G) ≅ α :=
  ext (fun X => ρ_ (α.app X)) (by simp)



instance _root_.PseudoFunctor.instBicategory : Bicategory (B ⥤ᵖ B₂) where
  id := id
  comp := comp
  whiskerLeft f α _ h := whiskerLeft f h
  whiskerRight := whiskerRight
  associator {F G H I} := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft_id := by intros; ext X; simp
  whiskerLeft_comp := by intros; ext X; simp
  id_whiskerLeft := by intros; ext X; simp
  comp_whiskerLeft := by intros; ext X; simp
  id_whiskerRight := by intros; ext X; simp
  comp_whiskerRight := by intros; ext X; simp
  whiskerRight_id := by intros; ext X; simp
  whiskerRight_comp := by intros; ext X; simp
  whisker_assoc := by intros; ext X; simp
  whisker_exchange := by intros; ext X; simpa using whisker_exchange _ _
  pentagon := by intros; ext X; simp
  triangle := by intros; ext X; simp

/--
info: PseudoFunctor.instBicategory.{w, w₂, v, v₂, u, u₂} {B : Type u} [Bicategory B] {B₂ : Type u₂} [Bicategory B₂] :
  Bicategory (B ⥤ᵖ B₂)
-/
#guard_msgs in
#check PseudoFunctor.instBicategory
/--
info: 'PseudoFunctor.instBicategory' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms PseudoFunctor.instBicategory

end PseudoNatTrans

end PseudoNatTrans

end CategoryTheory.Bicategory
