import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.Opposites

/-!
given a strict bicategory B, we get a functor `Bᵒᵖ ⥤ B ⥤ Cat`
-/

universe w w₂ w₃ v v₂ v₃ u u₂ u₃
namespace CategoryTheory
variable (B : Type u) [Bicategory.{w, v} B]
namespace Bicategory

section
def coyoneda [Bicategory.Strict B] : Bᵒᵖ ⥤ B ⥤ Cat where
  obj X := {
    obj Y := .of <| X.unop ⟶ Y
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

@[simp]
lemma eqToHom_mod (h : α = β) (X : B) :
    (eqToHom h).mod X = eqToHom congr(($h).app X) := by
  cases h
  simp


instance [∀ X Y : B₂, Quiver.IsThin (X ⟶ Y)] : Quiver.IsThin (F ⟶ G) :=
  fun α β => {
    allEq a b := by
      ext X
      rename_i h
      apply Subsingleton.elim
  }

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

@[simps]
def _root_.CategoryTheory.Iso.mod {α β : F ⟶ G} (e : α ≅ β) (X : B) : α.app X ≅ β.app X where
  hom := e.hom.mod X
  inv := e.inv.mod X
  hom_inv_id := congr(($e.hom_inv_id).mod X)
  inv_hom_id := congr(($e.inv_hom_id).mod X)

lemma _root_.CategoryTheory.Iso.mod_hom_naturality {α β : F ⟶ G} (e : α ≅ β) {X Y : B} (f : X ⟶ Y) :
    (e.mod X).hom ▷ G.map f ≫ (β.app₂ f).inv = (α.app₂ f).inv ≫ F.map f ◁ (e.mod Y).hom :=
  e.hom.mod_naturality f

lemma _root_.CategoryTheory.Iso.mod_inv_naturality {α β : F ⟶ G} (e : α ≅ β) {X Y : B} (f : X ⟶ Y) :
    (e.mod X).inv ▷ G.map f ≫ (α.app₂ f).inv = (β.app₂ f).inv ≫ F.map f ◁ (e.mod Y).inv :=
  e.inv.mod_naturality f

def ext! {α β : F ⟶ G} (happ : ∀ X, α.app X = β.app X) (happ₂ : ∀ {X Y : B} (f : X ⟶ Y),
  (α.app₂ f).hom = eqToHom congr(F.map f ≫ $(happ Y)) ≫ (β.app₂ f).hom ≫
    eqToHom (congr($(happ X) ≫ G.map f)).symm) : α = β := by
  cases α;cases β;
  simp at happ happ₂ ⊢
  cases funext happ
  simp_all
  congr
  ext X Y f
  rw [happ₂]


@[reassoc]
def associativity_symm (α : F ⟶ G) {X₁ X₂ X₃} (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃) :
    (α.app X₁) ◁ (G.mapComp f g).inv ≫ (α.app₂ (f ≫ g)).inv =
    (α_ _ _ _).inv ≫ ((α.app₂ f).inv ▷ (G.map g)) ≫ (α_ _ _ _).hom ≫
    (F.map f ◁ (α.app₂ g).inv) ≫ (α_ _ _ _).inv ≫ (F.mapComp f g).inv ▷ _ := by
  simp [associativity]

def comp {H : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) : F ⟶ H where
  app X := α.app X ≫ β.app X
  app₂ {X Y} f := (associator _ _ _).symm ≪≫ whiskerRightIso (α.app₂ _) (β.app Y) ≪≫
    (associator _ _ _) ≪≫ whiskerLeftIso _ (β.app₂ _) ≪≫ (associator _ _ _).symm
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
def id : F ⟶ F where
  app X := 𝟙 _
  app₂ {X Y} f := (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm

def whiskerLeft {H : B ⥤ᵖ B₂} (γ : H ⟶ F) (a : α ⟶ β) : comp γ α ⟶ comp γ β where
  mod X := γ.app X ◁ a.mod X
  mod_naturality {X Y} f := by
    simp only [comp, whisker_assoc, Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv,
      Category.assoc, whiskerRightIso_inv, Iso.inv_hom_id_assoc, Iso.cancel_iso_hom_left]
    rw [← whiskerLeft_comp_assoc,a.mod_naturality]
    simp only [whiskerLeft_comp, Category.assoc]
    rw [@associator_inv_naturality_right_assoc,whisker_exchange_assoc]
    simp

def whiskerRight {H : B ⥤ᵖ B₂} (a : α ⟶ β) (γ : G ⟶ H) : comp α γ ⟶ comp β γ where
  mod X := a.mod X ▷ γ.app X
  mod_naturality {X Y} f := by
    simp only [comp, Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv, Category.assoc,
      whiskerRightIso_inv]
    rw [@associator_naturality_left_assoc,← whisker_exchange_assoc]
    simp only [whiskerRight_comp, Category.assoc, Iso.hom_inv_id_assoc, Iso.cancel_iso_hom_left]
    rw [← comp_whiskerRight_assoc,a.mod_naturality]
    simp

-- variable (α β) in
def associator {F G H I : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ I) :
    comp (comp α β) γ ≅ comp α (comp β γ) :=
  ext (fun X => α_ (α.app X) (β.app X) (γ.app X)) (by simp [comp])

variable (α) in
def leftUnitor : comp (id F) α ≅ α :=
  ext (fun X => λ_ (α.app X)) (by simp [comp, id])

variable (α) in
def rightUnitor : comp α (id G) ≅ α :=
  ext (fun X => ρ_ (α.app X)) (by simp [comp, id])

instance _root_.Pseudofunctor.instBicategory : Bicategory (B ⥤ᵖ B₂) where
  id := id
  comp := comp
  whiskerLeft f α _ h := whiskerLeft f h
  whiskerRight := whiskerRight
  associator {F G H I} := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whiskerLeft_id := by intros; ext X; simp [comp, whiskerLeft]
  whiskerLeft_comp := by intros; ext X; simp [whiskerLeft]
  id_whiskerLeft := by intros; ext X; simp [comp, id, whiskerLeft, leftUnitor]
  comp_whiskerLeft := by intros; ext X; simp [comp, whiskerLeft, associator]
  id_whiskerRight := by intros; ext X; simp [comp, whiskerRight]
  comp_whiskerRight := by intros; ext X; simp [whiskerRight]
  whiskerRight_id := by intros; ext X; simp [id, whiskerRight, rightUnitor]
  whiskerRight_comp := by intros; ext X; simp [comp, whiskerRight, associator]
  whisker_assoc := by intros; ext X; simp [whiskerLeft, whiskerRight, associator]
  whisker_exchange := by intros; ext X; simpa [whiskerLeft, whiskerRight] using whisker_exchange _ _
  pentagon := by intros; ext X; simp [comp, whiskerLeft, whiskerRight, associator]
  triangle := by intros; ext X; simp [id, whiskerLeft, whiskerRight, leftUnitor, rightUnitor,
    associator]

@[simp]
lemma comp_app {H : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) (X : B) :
  (α ≫ β).app X = α.app X ≫ β.app X := rfl

@[simp]
lemma comp_app₂ {H : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) {X Y : B} (f : X ⟶ Y) :
  (α ≫ β).app₂ f = (α_ _ _ _).symm ≪≫ whiskerRightIso (α.app₂ f) (β.app Y) ≪≫
    (α_ _ _ _) ≪≫ whiskerLeftIso _ (β.app₂ _) ≪≫ (α_ _ _ _).symm := rfl

@[simp]
lemma comp_app₂_hom {H : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) {X Y : B} (f : X ⟶ Y) :
  ((α ≫ β).app₂ f).hom = (α_ _ _ _).inv ≫ (α.app₂ f).hom ▷ (β.app Y) ≫
    (α_ _ _ _).hom ≫ _ ◁ (β.app₂ f).hom ≫ (α_ _ _ _).inv := rfl

@[simp]
lemma comp_app₂_inv {H : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) {X Y : B} (f : X ⟶ Y) :
  ((α ≫ β).app₂ f).inv = (α_ _ _ _).hom ≫ _ ◁ (β.app₂ f).inv ≫
    (α_ _ _ _).inv ≫ (α.app₂ f).inv ▷ (β.app Y) ≫ (α_ _ _ _).hom := by
  dsimp
  simp only [Category.assoc]

variable (F) in
@[simp]
lemma id_app (X : B) : (𝟙 F : F ⟶ F).app X = 𝟙 (F.obj X) := rfl

@[simp]
lemma id_app₂ {X Y : B} (f : X ⟶ Y) :
    (𝟙 F : F ⟶ F).app₂ f = (ρ_ (F.map f)) ≪≫ (λ_ (F.map f)).symm := rfl

@[simp]
lemma id_app₂_hom {X Y : B} (f : X ⟶ Y) :
    ((𝟙 F : F ⟶ F).app₂ f).hom = (ρ_ (F.map f)).hom ≫ (λ_ (F.map f)).inv := rfl

@[simp]
lemma id_app₂_inv {X Y : B} (f : X ⟶ Y) :
    ((𝟙 F : F ⟶ F).app₂ f).inv = (λ_ (F.map f)).hom ≫ (ρ_ (F.map f)).inv := rfl


@[simp]
lemma whiskerLeft_mod {H : B ⥤ᵖ B₂} (γ : H ⟶ F) (a : α ⟶ β) (X : B) :
  (γ ◁ a).mod X = γ.app X ◁ a.mod X := rfl

@[simp]
lemma whiskerRight_mod {H : B ⥤ᵖ B₂} (a : α ⟶ β) (γ : G ⟶ H) (X : B) :
  (a ▷ γ).mod X = a.mod X ▷ γ.app X := rfl

@[simp]
lemma associator_mod {F G H I : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ I) (X : B) :
  (α_ α β γ).mod X = α_ (α.app X) (β.app X) (γ.app X) := rfl

@[simp]
lemma associator_hom_mod {F G H I : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ I) (X : B) :
  (α_ α β γ).hom.mod X = (α_ (α.app X) (β.app X) (γ.app X)).hom := rfl

@[simp]
lemma associator_inv_mod {F G H I : B ⥤ᵖ B₂} (α : F ⟶ G) (β : G ⟶ H) (γ : H ⟶ I) (X : B) :
  (α_ α β γ).inv.mod X = (α_ (α.app X) (β.app X) (γ.app X)).inv := rfl

variable (α) in
@[simp]
lemma leftUnitor_mod (X : B) : (λ_ α).mod X = λ_ (α.app X) := rfl

variable (α) in
@[simp]
lemma leftUnitor_hom_mod (X : B) : (λ_ α).hom.mod X = (λ_ (α.app X)).hom := rfl

variable (α) in
@[simp]
lemma leftUnitor_inv_mod (X : B) : (λ_ α).inv.mod X = (λ_ (α.app X)).inv := rfl

variable (α) in
@[simp]
lemma rightUnitor_mod (X : B) : (ρ_ α).mod X = ρ_ (α.app X) := rfl

variable (α) in
@[simp]
lemma rightUnitor_hom_mod (X : B) : (ρ_ α).hom.mod X = (ρ_ (α.app X)).hom := rfl

variable (α) in
@[simp]
lemma rightUnitor_inv_mod (X : B) : (ρ_ α).inv.mod X = (ρ_ (α.app X)).inv := rfl

instance _root_.Pseudofunctor.instBicategoryStrict [Bicategory.Strict B₂] :
  Bicategory.Strict (B ⥤ᵖ B₂) where
    id_comp := by
      intros
      fapply PseudoNatTrans.ext!
      · intro X
        simp
      · intro X Y f
        simp only [comp_app, id_app, comp_app₂, id_app₂, Iso.trans_hom, Iso.symm_hom,
          whiskerRightIso_hom, comp_whiskerRight, leftUnitor_inv_whiskerRight, whiskerLeftIso_hom,
          id_whiskerLeft, Category.assoc, Iso.inv_hom_id_assoc, triangle_assoc_comp_right_assoc]
        simp [Strict.leftUnitor_eqToIso, Strict.associator_eqToIso]
    comp_id := by
      intros
      fapply PseudoNatTrans.ext!
      · intro X
        simp
      · intros
        simp only [comp_app, id_app, comp_app₂, id_app₂, Iso.trans_hom, Iso.symm_hom,
          whiskerRightIso_hom, whiskerRight_id, whiskerLeftIso_hom, whiskerLeft_comp,
          whiskerLeft_rightUnitor, Category.assoc, triangle_assoc_comp_left_inv,
          Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
        simp [Strict.rightUnitor_eqToIso, Strict.associator_eqToIso]
    assoc f g h := by
      -- simp [(· ≫ ·)]
      apply PseudoNatTrans.ext!
      · simp [Strict.associator_eqToIso]
      · simp
    leftUnitor_eqToIso := by
      intro F G α
      ext X
      simp [Strict.leftUnitor_eqToIso]
    rightUnitor_eqToIso := by
      intros
      ext X
      simp [Strict.rightUnitor_eqToIso]
    associator_eqToIso := by
      intros
      ext X
      simp [Strict.associator_eqToIso]

end PseudoNatTrans

end PseudoNatTrans
end Bicategory
section Cat
open Bicategory

def NatTrans.toCatHom₂ {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {F G : C ⥤ D} (η : F ⟶ G) : (F.toCatHom : Cat.of C ⟶ Cat.of D) ⟶ G.toCatHom :=
  η

def NatTrans.ofCatHom₂ {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {F G : C ⥤ D} (η : F.toCatHom ⟶ G.toCatHom) :
  F ⟶ G := η

@[simp]
lemma NatTrans.ofCatHom₂_toCatHom₂ {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {F G : C ⥤ D} (η : F ⟶ G) : NatTrans.ofCatHom₂ η.toCatHom₂ = η := rfl


@[ext]
lemma ext {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {F G : C ⥤ D} (η₁ η₂ : F.toCatHom ⟶ G.toCatHom)
    (h : NatTrans.ofCatHom₂ η₁ = NatTrans.ofCatHom₂ η₂) : η₁ = η₂ := h

@[simp]
lemma NatTrans.ofCatHom₂_id {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D) : NatTrans.ofCatHom₂ (𝟙 F.toCatHom) = 𝟙 F := rfl

@[simp]
lemma NatTrans.ofCatHom₂_comp {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  {F G H : C ⥤ D} (η₁ : F.toCatHom ⟶ G.toCatHom) (η₂ : G.toCatHom ⟶ H.toCatHom) :
    NatTrans.ofCatHom₂ (η₁ ≫ η₂) = NatTrans.ofCatHom₂ η₁ ≫ NatTrans.ofCatHom₂ η₂ := rfl

@[simp]
lemma NatTrans.ofCatHom₂_whiskerLeft {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {E : Type u} [Category.{v} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G.toCatHom ⟶ H.toCatHom) :
    NatTrans.ofCatHom₂ (F.toCatHom ◁ η) = F.whiskerLeft (NatTrans.ofCatHom₂ η) := rfl

@[simp]
lemma NatTrans.ofCatHom₂_associator_hom {A C D E : Type u} [Category.{v} A]
  [Category.{v} C] [Category.{v} D] [Category.{v} E] (F : A ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
  NatTrans.ofCatHom₂ (α_ F.toCatHom G.toCatHom H.toCatHom).hom =
    (Functor.associator F G H).hom := rfl

@[simp]
lemma NatTrans.ofCatHom₂_associator_inv {A C D E : Type u} [Category.{v} A]
  [Category.{v} C] [Category.{v} D] [Category.{v} E] (F : A ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
  NatTrans.ofCatHom₂ (α_ F.toCatHom G.toCatHom H.toCatHom).inv =
    (Functor.associator F G H).inv := rfl

@[simp]
lemma NatTrans.ofCatHom₂_leftUnitor_hom {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D) : NatTrans.ofCatHom₂ (λ_ F.toCatHom).hom = (Functor.leftUnitor F).hom := rfl

@[simp]
lemma NatTrans.ofCatHom₂_leftUnitor_inv {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D) : NatTrans.ofCatHom₂ (λ_ F.toCatHom).inv = (Functor.leftUnitor F).inv := rfl

@[simp]
lemma NatTrans.ofCatHom₂_rightUnitor_hom {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D) : NatTrans.ofCatHom₂ (ρ_ F.toCatHom).hom = (Functor.rightUnitor F).hom := rfl

@[simp]
lemma NatTrans.ofCatHom₂_rightUnitor_inv {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (F : C ⥤ D) : NatTrans.ofCatHom₂ (ρ_ F.toCatHom).inv = (Functor.rightUnitor F).inv := rfl

-- @[simp]
-- lemma NatTrans.ofCatHom₂_associator_inv {A C D E : Type u} [Category.{v} A]
--   [Category.{v} C] [Category.{v} D] [Category.{v} E] (F : A ⥤ C) (G : C ⥤ D) (H : D ⥤ E) :
--   NatTrans.ofCatHom₂ (α_ F.toCatHom G.toCatHom H.toCatHom).inv =
--     (Functor.associator F G H).inv := rfl



-- example {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
--     {E : Type u} [Category.{v} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G.toCatHom ⟶ H.toCatHom) :
--     True := by
--   have := NatTrans.ofCatHom₂_whiskerLeft F η
--   simp only [Cat.of_α] at this

@[simp]
lemma NatTrans.ofCatHom₂_whiskerRight {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {E : Type u} [Category.{v} E] {F G : C ⥤ D} (η : F.toCatHom ⟶ G.toCatHom) (H : D ⥤ E) :
    NatTrans.ofCatHom₂ (η ▷ H.toCatHom) = Functor.whiskerRight (NatTrans.ofCatHom₂ η) H := rfl

-- @[simp]
-- lemma NatTrans.toCatHom₂_whiskerLeft {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
--     {E : Type u} [Category.{v} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G ⟶ H) :
--     NatTrans.toCatHom₂ (Functor.whiskerLeft F η) = F.toCatHom ◁ (NatTrans.toCatHom₂ η) := rfl

@[simps]
def NatIso.toCatIso₂ {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {F G : C ⥤ D} (η : F ≅ G) : F.toCatHom ≅ G.toCatHom where
  hom := η.hom.toCatHom₂
  inv := η.inv.toCatHom₂
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

@[simps]
def NatIso.ofCatIso₂ {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
    {F G : C ⥤ D} (η : F.toCatHom ≅ G.toCatHom) : F ≅ G where
  hom := NatTrans.ofCatHom₂ η.hom
  inv := NatTrans.ofCatHom₂ η.inv
  hom_inv_id := by rw [← NatTrans.ofCatHom₂_comp]; simp
  inv_hom_id := by rw [← NatTrans.ofCatHom₂_comp]; simp

-- lemma NatIso.ofCatIso₂_whiskerLeft {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
--     {E : Type u} [Category.{v} E] (F : C ⥤ D) {G H : D ⥤ E} (η : G.toCatHom) :
--     NatIso.ofCatIso₂ (F.toCatHom ◁ _) = whiskerLeft _ := rfl

end Cat


namespace Pseudofunctor
open Bicategory
variable {B}
variable {B₂ : Type u₂} [Bicategory.{w₂, v₂} B₂] {B₃ : Type u₃} [Bicategory.{w₃, v₃} B₃]
section flip

-- we don't use @[simps] here because it generates annoyingly long lemma names.
def flipObj (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) (Y : B₂) : B ⥤ᵖ B₃ where
  obj X := (F.obj X).obj Y
  map {X₁ X₂} f := (F.map f).app Y
  map₂ {X₁ X₂} {f₁ f₂} η := (F.map₂ η).mod Y
  map₂_id {X₁ X₂} f := by simp
  map₂_comp {X₁ X₂} {f₁ f₂ f₃} η θ := by simp
  mapId X := (F.mapId X).mod Y
  mapComp {X₁ X₂ X₃} f₁ f₂ := (F.mapComp f₁ f₂).mod Y
  map₂_whisker_left {X₁ X₂ X₃} f {g₁ g₂} η := by
    simp only [Pseudofunctor.map₂_whisker_left, PseudoModification.comp_mod_app, Iso.mod_hom,
      Iso.mod_inv]
    rfl
  map₂_whisker_right {X₁ X₂ X₃} {f₁ f₂} η g := by simp
  map₂_associator := by intros; simp
  map₂_left_unitor := by intros; simp
  map₂_right_unitor := by intros; simp

@[simp]
lemma flipObj_obj (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) (Y : B₂) (X : B) :
  (F.flipObj Y).obj X = (F.obj X).obj Y := rfl

@[simp]
lemma flipObj_map (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) (Y : B₂) {X₁ X₂ : B} (f : X₁ ⟶ X₂) :
  (F.flipObj Y).map f = (F.map f).app Y := rfl

@[simp]
lemma flipObj_map₂ (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) (Y : B₂) {X₁ X₂ : B} {f₁ f₂ : X₁ ⟶ X₂} (η : f₁ ⟶ f₂) :
  (F.flipObj Y).map₂ η = (F.map₂ η).mod Y := rfl

@[simp]
lemma flipObj_mapId (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) (Y : B₂) (X : B) : (F.flipObj Y).mapId X =
  (F.mapId X).mod Y := rfl

@[simp]
lemma flipObj_mapComp (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) (Y : B₂) {X₁ X₂ X₃ : B} (f₁ : X₁ ⟶ X₂) (f₂ : X₂ ⟶ X₃) :
  (F.flipObj Y).mapComp f₁ f₂ = (F.mapComp f₁ f₂).mod Y := rfl

@[simps]
def flipMap (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) {Y₁ Y₂ : B₂} (g : Y₁ ⟶ Y₂) : flipObj F Y₁ ⟶ flipObj F Y₂ where
  app X := (F.obj X).map g
  app₂ {X₁ X₂} f := ((F.map f).app₂ g).symm
  app₂_naturality {X₁ X₂} {f₁ f₂} η := (F.map₂ η).mod_naturality g
  unitality X := by
    dsimp only [flipObj_obj, flipObj_map, flipObj_mapId, Iso.mod_inv, Iso.symm_inv]
    have := (F.mapId X).mod_inv_naturality g
    rw [Iso.comp_inv_eq, Iso.mod_inv] at this
    rw [this]
    simp
  associativity {X₁ X₂ X₃} f₁ f₂ := by
    dsimp only [flipObj_obj, flipObj_map, Iso.symm_inv, flipObj_mapComp, Iso.mod_inv]
    have := (F.mapComp f₁ f₂).mod_inv_naturality g
    rw [Iso.comp_inv_eq, Iso.mod_inv] at this
    rw [this]
    simp

@[simps]
def flipMap₂ (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) {Y₁ Y₂ : B₂} {g₁ g₂ : Y₁ ⟶ Y₂} (η : g₁ ⟶ g₂) :
    flipMap F g₁ ⟶ flipMap F g₂ where
  mod X := (F.obj X).map₂ η
  mod_naturality {_X₁ _X₂} f := (F.map f).app₂_naturality η

-- again, no @[simps].
def flip (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) : B₂ ⥤ᵖ B ⥤ᵖ B₃ where
  obj Y := flipObj F Y
  map {Y₁ Y₂} g := flipMap F g
  map₂ {Y₁ Y₂} {g₁ g₂} η := flipMap₂ F η
  map₂_id {Y₁ Y₂} g:= by
    ext X
    exact (F.obj X).map₂_id g
  map₂_comp {Y₁ Y₂} {g₁ g₂ g₃} h₁ h₂ := by
    ext X
    exact (F.obj X).map₂_comp h₁ h₂
  mapId Y := PseudoNatTrans.ext (fun X => (F.obj X).mapId Y) (by
    dsimp only [flipObj_obj, flipMap_app, flipObj_map, PseudoNatTrans.id_app,
      PseudoNatTrans.id_app₂, Iso.trans_inv, Iso.symm_inv, flipMap_app₂]
    intro X₁ X₂ f
    have := (F.map f).unitality Y
    rw [Iso.eq_comp_inv,Category.assoc,← Iso.eq_inv_comp,← whiskerLeftIso_inv,
      Iso.eq_comp_inv,whiskerLeftIso_hom] at this
    rw [← this]
    simp
  )
  mapComp {Y₁ Y₂ Y₃} g₁ g₂ := PseudoNatTrans.ext (fun X => (F.obj X).mapComp g₁ g₂) (by
    dsimp only [flipObj_obj, flipMap_app, flipObj_map, PseudoNatTrans.comp_app,
      PseudoNatTrans.comp_app₂, flipMap_app₂, Iso.trans_inv, Iso.symm_inv, whiskerLeftIso_inv,
      whiskerRightIso_inv]
    intro X₁ X₂ f
    have := (F.map f).associativity g₁ g₂
    simp_rw [← whiskerLeftIso_inv,← whiskerRightIso_inv] at this
    rw [← Iso.inv_comp_eq,Iso.eq_inv_comp] at this
    rw [← Iso.inv_comp_eq, ← this]
    simp
    )
  map₂_whisker_left := by intros; ext X; simp
  map₂_whisker_right := by intros; ext X; simp
  map₂_associator := by intros; ext X; simp
  map₂_left_unitor := by intros; ext X; simp
  map₂_right_unitor := by intros; ext X; simp

@[simp]
lemma flip_obj (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) (Y : B₂) : F.flip.obj Y = (F.flipObj Y) := rfl

@[simp]
lemma flip_map (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) {Y₁ Y₂ : B₂} (g : Y₁ ⟶ Y₂) :
    F.flip.map g = F.flipMap g := rfl

@[simp]
lemma flip_map₂ (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) {Y₁ Y₂ : B₂} {g₁ g₂ : Y₁ ⟶ Y₂} (η : g₁ ⟶ g₂) :
  F.flip.map₂ η = F.flipMap₂ η := rfl

@[simp]
lemma flip_mapId (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) (Y : B₂) :
  F.flip.mapId Y = PseudoNatTrans.ext (fun X => (F.obj X).mapId Y) (flip._proof_3 F Y) := rfl

@[simp]
lemma flip_mapComp (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) {Y₁ Y₂ Y₃ : B₂} (g₁ : Y₁ ⟶ Y₂) (g₂ : Y₂ ⟶ Y₃) :
    F.flip.mapComp g₁ g₂ = PseudoNatTrans.ext (fun X => (F.obj X).mapComp g₁ g₂)
    (flip._proof_4 F g₁ g₂) := rfl

@[simp]
lemma flip_flip (F : B ⥤ᵖ B₂ ⥤ᵖ B₃) : F.flip.flip = F := by -- actually rfl, but that takes long.
  cases F
  rw [flip, flip]
  congr

end flip
end Pseudofunctor

section coyoneda

open Bicategory
variable {B}

def Bicategory.pseudoCoyonedaObj (X : Bᵒᵖ) : B ⥤ᵖ Cat where
  obj Y := .of (X.unop ⟶ Y)
  map {Y₁ Y₂} f₁ := Functor.toCatHom ((Bicategory.postcomp X.unop f₁))
  map₂ {Y₁ Y₂} {f₁ f₂} η :=
    NatTrans.toCatHom₂ ((Bicategory.postcomposing X.unop Y₁ Y₂).map η)
  map₂_id {Y₁ Y₂} f := by
    ext f₂
    simp
  map₂_comp {Y₁ Y₂} {f₁ f₂ f₃} η₁ η₂ := by
    ext f₄
    simp [NatTrans.comp_app _ _]
  mapId Y := NatIso.toCatIso₂ <| Bicategory.rightUnitorNatIso X.unop Y
  mapComp {Y₁ Y₂ Y₃} f₁ f₂ := NatIso.toCatIso₂ (Bicategory.associatorNatIsoLeft X.unop f₁ f₂).symm
  map₂_whisker_left := by intros; ext f₂; simp [NatTrans.ofCatHom₂_whiskerLeft _ _]
  map₂_whisker_right := by intros; ext f₂; simp [NatTrans.ofCatHom₂_whiskerRight _ _]
  map₂_associator := by intros; ext; simp [NatTrans.ofCatHom₂_toCatHom₂, NatIso.toCatIso₂_hom,
      NatTrans.ofCatHom₂_whiskerRight _ _, NatTrans.ofCatHom₂_associator_hom _ _ _,
      NatTrans.ofCatHom₂_whiskerLeft _ _, Category.id_comp ((α_ _ _ _).hom ≫ _)]
  map₂_left_unitor := by intros; ext f₂; simp [NatTrans.ofCatHom₂_whiskerRight _ _,
    NatTrans.ofCatHom₂_leftUnitor_hom _]
  map₂_right_unitor := by intros; ext f₂; simp [NatTrans.ofCatHom₂_whiskerLeft _ _,
    NatTrans.ofCatHom₂_rightUnitor_hom _, Category.comp_id (ρ_ (f₂ ≫ _)).hom]

@[simp]
lemma Bicategory.pseudoCoyonedaObj_obj {X : Bᵒᵖ} (Y : B) :
  (pseudoCoyonedaObj X).obj Y = .of (X.unop ⟶ Y) := rfl

@[simp]
lemma Bicategory.pseudoCoyonedaObj_map {X : Bᵒᵖ} {Y₁ Y₂ : B} (g : Y₁ ⟶ Y₂) :
  (pseudoCoyonedaObj X).map g = (Bicategory.postcomp X.unop g).toCatHom := rfl

@[simp]
lemma Bicategory.pseudoCoyonedaObj_map2 {X : Bᵒᵖ} {Y₁ Y₂ : B} {g₁ g₂ : Y₁ ⟶ Y₂}
    (η : g₁ ⟶ g₂) : (pseudoCoyonedaObj X).map₂ η =
      NatTrans.toCatHom₂ ((Bicategory.postcomposing X.unop Y₁ Y₂).map η) := rfl


@[simps]
def Bicategory.pseudoCoyonedaMap {X₁ X₂ : Bᵒᵖ} (f : X₁ ⟶ X₂) :
    pseudoCoyonedaObj X₁ ⟶ pseudoCoyonedaObj X₂ where
  app Y := {
    obj f₁ := f.unop ≫ f₁
    map {f₁ f₂} η := f.unop ◁ η
    map_id f₁ := whiskerLeft_id f.unop f₁
    map_comp {f₁ f₂ f₃} η₁ η₂ := whiskerLeft_comp f.unop η₁ η₂
  }
  app₂ {Y₁ Y₂} f₂ := NatIso.ofComponents (fun f₃ => (α_ f.unop f₃ f₂).symm) (by intros; simp)
  app₂_naturality {X₁ X₂} {f₁ f₂} η := by ext f₃; simp
  unitality X := by
    ext f₃
    simp_rw [Cat.comp_app, Cat.rightUnitor_hom_app, Cat.leftUnitor_inv_app, Cat.whiskerLeft_app]
    simp
  associativity {X₁ X₂ X₃} f₁ f₂ := by
    ext f₃
    simp_rw [Cat.comp_app, Cat.associator_hom_app,Cat.associator_inv_app]
    simp

@[simps]
def Bicategory.pseudoCoyonedaMap₂ {X₁ X₂ : Bᵒᵖ} {f₁ f₂ : X₁ ⟶ X₂} (η : f₁ ⟶ f₂) :
    pseudoCoyonedaMap f₁ ⟶ pseudoCoyonedaMap f₂ where
  mod Y := {
    app f₃ := η.unop2 ▷ f₃
    naturality {f₃ f₄} η₂ := whisker_exchange η.unop2 η₂
  }
  mod_naturality {Y₁ Y₂} g := by ext g₂; simp

@[simps]
def Bicategory.pseudoCoyoneda : Bᵒᵖ ⥤ᵖ B ⥤ᵖ Cat where
  obj X := pseudoCoyonedaObj X
  map {X₁ X₂} f := pseudoCoyonedaMap f
  map₂ {X₁ X₂} {f₁ f₂} η := pseudoCoyonedaMap₂ η
  map₂_id {X₁ X₂} f:= by ext Y g; simp
  map₂_comp {X₁ X₂} {f₁ f₂ f₃} η η₂ := by ext Y g; simp
  mapId X := PseudoNatTrans.ext (fun Y => NatIso.ofComponents (fun g => λ_ g) (by intros; simp)) (by
    intros
    ext g
    simp [Cat.comp_app,Cat.rightUnitor_inv_app,Cat.leftUnitor_hom_app])
  mapComp {X₁ X₂ X₂} f₁ f₂ := PseudoNatTrans.ext
    (fun Y => NatIso.ofComponents (fun g => α_ f₂.unop f₁.unop g)) (by
    intros
    ext g
    simp [Cat.comp_app, Cat.associator_hom_app,Cat.associator_inv_app]
    )
  map₂_whisker_left := by intros; ext X f; simp
  map₂_whisker_right := by intros; ext X f; simp
  map₂_associator := by intros; ext X f; simp [Cat.comp_app, Cat.associator_hom_app]
  map₂_left_unitor := by intros; ext X f; simp [Cat.comp_app, Cat.leftUnitor_hom_app]
  map₂_right_unitor := by intros; ext X f; simp [Cat.comp_app, Cat.rightUnitor_hom_app]

end coyoneda


end CategoryTheory
