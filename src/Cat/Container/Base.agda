{-# OPTIONS --cubical-compatible #-}
module Cat.Container.Base where
open import Cubical.Foundations.Prelude
open import Categories.Category.Core
open import Categories.Functor.Core

data CatContainerStr {ℓSo ℓSh ℓSe ℓPo ℓPh ℓPe : Level} : Type where
  S : Category ℓSo ℓSh ℓSe
  P : Functor S (Category ℓPo ℓPh ℓPe)

CatContainerCat : 2-Category _ _ _ _
CatContainerCat = ?
