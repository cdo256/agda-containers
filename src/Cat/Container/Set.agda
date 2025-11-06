{-# OPTIONS --lossy-unification --cubical #-}
module Cat.Container.Set where
open import Data.Product hiding (Σ-syntax; swap)
open import Agda.Primitive
-- open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude
open import Cubical.Categories.Category
open import Cubical.Relation.Nullary
-- open import Categories.2-Category
-- open import Categories.Category.Instance.Cats
open import Cubical.Categories.Instances.Categories
-- open import Categories.Category.Monoidal.Instance.StrictCats
open import Cubical.Categories.Functor
-- open import Categories.Functor.Equivalence
-- open import Categories.NaturalTransformation.Core using (NaturalTransformation) renaming (id to idN)
-- open import Categories.NaturalTransformation.Equivalence using () renaming (_≃_ to _≈N_) 
open import Cubical.Foundations.Function

open import Cubical.Categories.NaturalTransformation.Base
open import Cubical.Categories.NaturalTransformation.Properties

private
  variable
    ℓ ℓ' : Level
    A : Type ℓ
    B : Type ℓ'

Singleton : ∀ {ℓ} {A : Type ℓ} → A → Type _
Singleton x = Σ[ y ∈ _ ] x ≡ y

inspect' : ∀ {ℓ} {A : Type ℓ} (x : A) → Singleton x
inspect' x = x , refl

module _ (A : Type ℓ) (_≟_ : Discrete A) where
  infixr 30 _∷_
  data HITSet  : Type (ℓ-suc (ℓ-suc ℓ)) where
    [] : HITSet
    _∷_ : A → HITSet → HITSet 
    swap : ∀ (x y : A) (xs : HITSet) → x ∷ y ∷ xs ≡ y ∷ x ∷ xs
    duplicate : (x : A) → (xs : HITSet ) → x ∷ xs ≡ x ∷ x ∷ xs

  ins : A → HITSet → HITSet
  ins x [] = x ∷ []
  ins x (y ∷ ys) = x ∷ y ∷ ys
  ins x (swap y z zs i) = cong (x ∷_) (swap y z zs) i
  ins x (duplicate y ys i) = cong (x ∷_) (duplicate y ys) i

  consMaybe : {P : Type ℓ'} → (x : A) (xs : HITSet) → Dec P → HITSet
  consMaybe x xs (yes _) = xs
  consMaybe x xs (no _) = x ∷ xs

  recurse-consMaybe : {B : Type ℓ'} {P : Dec B} (y z : A) (xs : HITSet) → y ∷ consMaybe z xs P ≡ consMaybe z (y ∷ xs) P
  recurse-consMaybe {P = yes p} y z xs = refl
  recurse-consMaybe {P = no ¬p} y z xs = {!refl!}

  del : A → HITSet → HITSet
  del x [] = []
  del x (y ∷ xs) = consMaybe y (del x xs) (x ≟ y)
  del x (swap y z zs i) = u (inspect' (x ≟ y)) i
    where
      v : Singleton (x ≟ z) → y ∷ consMaybe z (del x zs) (x ≟ z) ≡ consMaybe z (y ∷ del x zs) (x ≟ z)
      v (yes _ , p) = cong (y ∷_) (cong (consMaybe z (del x zs)) p)
                    ∙ cong (consMaybe z (y ∷ del x zs)) (sym p)
      v (no _ , p) = cong (y ∷_) (cong (consMaybe z (del x zs)) p)
                   ∙ swap y z (del x zs)
                   ∙ cong (consMaybe z (y ∷ del x zs)) (sym p)
      u : Singleton (x ≟ y)
              → consMaybe y (consMaybe z (del x zs) (x ≟ z)) (x ≟ y)
              ≡ consMaybe z (consMaybe y (del x zs) (x ≟ y)) (x ≟ z)
      u (yes _ , p) =
        consMaybe y (consMaybe z (del x zs) (x ≟ z)) (x ≟ y)
          ≡⟨ cong (λ ○ → consMaybe y (consMaybe z (del x zs) (x ≟ z)) ○) p ⟩
        consMaybe y (consMaybe z (del x zs) (x ≟ z)) (yes _)
          ≡⟨ refl ⟩
        consMaybe z (consMaybe y (del x zs) (yes _)) (x ≟ z)
          ≡⟨ sym (cong (λ ○ → consMaybe z (consMaybe y (del x zs) ○) (x ≟ z)) p) ⟩
        consMaybe z (consMaybe y (del x zs) (x ≟ y)) (x ≟ z) ∎ 
      u (no _ , p) =
        consMaybe y (consMaybe z (del x zs) (x ≟ z)) (x ≟ y)
          ≡⟨ cong (λ ○ → consMaybe y (consMaybe z (del x zs) (x ≟ z)) ○) p ⟩
        consMaybe y (consMaybe z (del x zs) (x ≟ z)) (no _)
          ≡⟨ v (inspect' (x ≟ z)) ⟩
        consMaybe z (consMaybe y (del x zs) (no _)) (x ≟ z)
          ≡⟨ sym (cong (λ ○ → consMaybe z (consMaybe y (del x zs) ○) (x ≟ z)) p) ⟩
        consMaybe z (consMaybe y (del x zs) (x ≟ y)) (x ≟ z) ∎ 
  del x (duplicate y ys i) = v (inspect' (x ≟ y)) i
    where
      v : Singleton (x ≟ y) → consMaybe y (del x ys) (x ≟ y) ≡ consMaybe y (consMaybe y (del x ys) (x ≟ y)) (x ≟ y)
      v (yes _ , p) = cong (consMaybe y (consMaybe y (del x ys) (x ≟ y))) (sym p)
      v (no _ , p) =
        consMaybe y (del x ys) (x ≟ y)
          ≡⟨ cong (consMaybe y (del x ys)) p ⟩
        consMaybe y (del x ys) (no _)
          ≡⟨ duplicate y (del x ys) ⟩
        consMaybe y (consMaybe y (del x ys) (no _)) (no _)
          ≡⟨ cong (λ ○ → consMaybe y (consMaybe y (del x ys) ○) ○) (sym p) ⟩
        consMaybe y (consMaybe y (del x ys) (x ≟ y)) (x ≟ y) ∎
