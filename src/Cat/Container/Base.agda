{-# OPTIONS --lossy-unification --cubical #-}
module Cat.Container.Base where
open import Data.Product hiding (Σ-syntax)
open import Agda.Primitive
-- open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
-- open import Categories.2-Category
-- open import Categories.Category.Instance.Cats
open import Cubical.Categories.Instances.Categories
open import Categories.Category.Monoidal.Instance.StrictCats
open import Cubical.Categories.Functor
-- open import Categories.Functor.Equivalence
-- open import Categories.NaturalTransformation.Core using (NaturalTransformation) renaming (id to idN)
-- open import Categories.NaturalTransformation.Equivalence using () renaming (_≃_ to _≈N_) 

open import Cubical.Categories.NaturalTransformation.Base

private
  variable
    ℓSo ℓSh ℓSe ℓPo ℓPh ℓPe : Level
    ℓ ℓ' ℓ'' ℓ''' : Level

module _ where
  open Category
  open Functor
  open NatTrans
  ●ᵛ-assoc : {C D : Category ℓ ℓ'} {F G H I : Functor C D}
           → (α : NatTrans F G) (β : NatTrans G H) (γ : NatTrans H I)
           → α ●ᵛ (β ●ᵛ γ) ≡ (α ●ᵛ β) ●ᵛ γ 
  ●ᵛ-assoc {C = C} {D = D} α β γ = makeNatTransPath (funExt p)
    where
      p : (x : C .ob) → N-ob (α ●ᵛ (β ●ᵛ γ)) x ≡ N-ob (α ●ᵛ β ●ᵛ γ) x
      p x = sym (D .⋆Assoc _ _ _)


module _ (ℓSo ℓSh ℓPo ℓPh : Level) where
  record CConObj : Type (ℓ-suc (ℓSo ⊔ ℓSh ⊔ ℓPo ⊔ ℓPh)) where
    constructor _◁C_
    field
      S : Category ℓSo ℓSh
      P : Functor S (CatCategory {ℓPo} {ℓPh})

  record CConHom (A B : CConObj) : Type (ℓ-suc (ℓSo ⊔ ℓSh ⊔ ℓPo ⊔ ℓPh)) where
    constructor _◁h_
    open CConObj A
    open CConObj B renaming (S to T; P to Q)
    field
      F : Functor S T
      σ : NatTrans (Q ∘F F) P

  ⟦_⟧ : (A : CConObj) → Type _
  ⟦ S ◁C P ⟧ = Σ[ s ∈ S .ob ] Functor (P .F-ob s .fst) CatCategory
    where
      open Category
      open Functor

  infixl 20 _∘h_
  _∘h_ : ∀ {A B C} → CConHom B C → CConHom A B → CConHom A C
  (F ◁h σ) ∘h (G ◁h τ) = (F ∘F G) ◁h (α ●ᵛ (σ ∘ˡ G) ●ᵛ τ)
    where α = pathToNatTrans F-assoc

  open Category
  CCon : Category _ _
  CCon .ob = CConObj
  CCon .Hom[_,_] = CConHom
  CCon .id {S ◁C P} = Id ◁h pathToNatTrans F-lUnit
  CCon ._⋆_ f g = g ∘h f
  CCon .⋆Assoc {x = A} {y = B} {z = C} {w = D} (F ◁h σ) (G ◁h τ) (H ◁h ρ) =
    (H ◁h ρ) ∘h ((G ◁h τ) ∘h (F ◁h σ))
      ≡⟨ refl ⟩
    (H ◁h ρ) ∘h ((G ∘F F) ◁h (α ●ᵛ (τ ∘ˡ F) ●ᵛ σ))
      ≡⟨ refl ⟩
    (H ∘F (G ∘F F)) ◁h (β ●ᵛ (ρ ∘ˡ (G ∘F F)) ●ᵛ (α ●ᵛ (τ ∘ˡ F) ●ᵛ σ))
      ≡⟨ cong₂ _◁h_ F-assoc trans≡ ⟩
    ((H ∘F G) ∘F F) ◁h (δ ●ᵛ ((γ ●ᵛ (ρ ∘ˡ G) ●ᵛ τ) ∘ˡ F) ●ᵛ σ)
      ≡⟨ refl ⟩
    ((H ∘F G) ◁h (γ ●ᵛ (ρ ∘ˡ G) ●ᵛ τ)) ∘h (F ◁h σ)
      ≡⟨ refl ⟩
    ((H ◁h ρ) ∘h (G ◁h τ)) ∘h (F ◁h σ) ∎
    where
      α : NatTrans (_ ∘F (G ∘F F)) ((_ ∘F G) ∘F F)
      α = pathToNatTrans F-assoc
      β : NatTrans (_ ∘F (H ∘F (G ∘F F))) ((_ ∘F H) ∘F (G ∘F F))
      β = pathToNatTrans F-assoc
      γ : NatTrans (_ ∘F (H ∘F G)) ((_ ∘F H) ∘F G) 
      γ = pathToNatTrans F-assoc
      δ : NatTrans (_ ∘F ((H ∘F G) ∘F F)) ((_ ∘F (H ∘F G)) ∘F F) 
      δ = pathToNatTrans F-assoc
      p : (β ●ᵛ (ρ ∘ˡ (G ∘F F))) ●ᵛ (α ●ᵛ (τ ∘ˡ F) ●ᵛ σ)
        ≡ {!!}
      p =
        (β ●ᵛ (ρ ∘ˡ (G ∘F F))) ●ᵛ ((α ●ᵛ (τ ∘ˡ F)) ●ᵛ σ)
          ≡⟨ {!●ᵛ-assoc ? ? ?!} ⟩ -- odd issue with universe levels
        ((β ●ᵛ (ρ ∘ˡ (G ∘F F))) ●ᵛ (α ●ᵛ (τ ∘ˡ F))) ●ᵛ σ
          ≡⟨ cong (_●ᵛ σ) (sym {!●ᵛ-assoc ? ? ?!}) ⟩ -- more universe level issues
        (β ●ᵛ ((ρ ∘ˡ (G ∘F F)) ●ᵛ (α ●ᵛ (τ ∘ˡ F)))) ●ᵛ σ
          ≡⟨ {!!} ⟩
        {!(β ●ᵛ ({!ρ ●ᵛ (idTrans (G ∘F F))!} ●ᵛ (α ●ᵛ (τ ●ᵛ (idTrans F))))) ●ᵛ σ!}
          ≡⟨ {!!} ⟩
        {!β ●ᵛ ρ ●ᵛ idTrans (G ∘F F) ●ᵛ α ●ᵛ τ ●ᵛ (idTrans F) ●ᵛ σ!} ∎ 
      trans≡ : (λ i → NatTrans (CConObj.P D ∘F F-assoc i) (CConObj.P A))
             [ (β ●ᵛ (ρ ∘ˡ (G ∘F F))) ●ᵛ (α ●ᵛ (τ ∘ˡ F) ●ᵛ σ)
             ≡ (δ ●ᵛ ((γ ●ᵛ (ρ ∘ˡ G) ●ᵛ τ) ∘ˡ F)) ●ᵛ σ ]
      trans≡ = makeNatTransPathP (λ i → CConObj.P D ∘F F-assoc i) (λ i → CConObj.P A)
        ({!p!} ◁ {!!} ▷ {!!})
  CCon .⋆IdL {x = S ◁C P} {y = T ◁C Q} (F ◁h σ) =
    (F ∘F Id) ◁h ((pathToNatTrans F-assoc ●ᵛ (σ ∘ˡ Id)) ●ᵛ pathToNatTrans F-lUnit)
      ≡⟨ cong₂ _◁h_ F-lUnit (makeNatTransPathP (cong (Q ∘F_) F-lUnit) refl p) ⟩
    F ◁h σ ∎
    where
      p : PathP
           (λ i →
              (x : S .ob) →
              Hom[ CatCategory , (Q ∘F F-lUnit i) .Functor.F-ob x ]
              (P .Functor.F-ob x))
           (NatTrans.N-ob
            (pathToNatTrans F-assoc ●ᵛ (σ ∘ˡ Id) ●ᵛ pathToNatTrans F-lUnit))
           (NatTrans.N-ob σ)
      p = {!!}
  CCon .⋆IdR = {!!}
  CCon .isSetHom = {!!}
  
