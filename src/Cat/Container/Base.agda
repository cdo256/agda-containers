{-# OPTIONS --cubical-compatible #-}
module Cat.Container.Base where
open import Data.Product hiding (Σ-syntax)
-- open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude
open import Categories.Category.Core
open import Categories.2-Category
open import Categories.Category.Instance.Cats
open import Categories.Category.Monoidal.Instance.StrictCats
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Equivalence
open import Categories.NaturalTransformation.Core using (NaturalTransformation) renaming (id to idN)
open import Categories.NaturalTransformation.Equivalence using () renaming (_≃_ to _≈N_) 

private
  variable
    ℓSo ℓSh ℓSe ℓPo ℓPh ℓPe : Level

module CCon (ℓSo ℓSh ℓSe ℓPo ℓPh ℓPe : Level) where

  record CConObj : Type _ where
    constructor _◁C_
    field
      S : Category ℓSo ℓSh ℓSe
      P : Functor S (Cats ℓPo ℓPh ℓPe)

  record CConHom (A B : CConObj) : Type _ where
    constructor _◁h_
    open CConObj A
    open CConObj B renaming (S to T; P to Q)
    field
      F : Functor S T
      σ : NaturalTransformation (Q ∘F F) P

  open Category
  CCon : Category _ _ _
  CCon .Obj = CConObj
  CCon ._⇒_ = CConHom
  _≈_ CCon {S ◁C P} {T ◁C Q} (F ◁h σ) (G ◁h τ) =
    Σ[ p ∈ F ≡F G ] PathP (λ i → NaturalTransformation (Q ∘F {!p i!}) P) {!!} {!!}
  CCon .id {S ◁C P} = idF ◁h subst2 NaturalTransformation {!!} {!!} {!!}
    where
    P≡P∘id : P ≡ P ∘F idF
    P≡P∘id i .Functor.F₀ x = {!!}
    P≡P∘id i .Functor.F₁ = {!!}
    P≡P∘id i .Functor.identity = {!!}
    P≡P∘id i .Functor.homomorphism = {!!}
    P≡P∘id i .Functor.F-resp-≈ = {!!}
  CCon ._∘_ = {!!}
  CCon .assoc = {!!}
  CCon .sym-assoc = {!!}
  CCon .identityˡ = {!!}
  CCon .identityʳ = {!!}
  CCon .identity² = {!!}
  CCon .equiv = {!!}
  CCon .∘-resp-≈ = {!!}
