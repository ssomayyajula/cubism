{-# OPTIONS --cubical #-}



open import Agda.Primitive using (_⊔_)
open import Agda.Primitive.Cubical public

open import Function

infix 30 ~
~ = primINeg

infixr 20 _∧_ _∨_
_∧_ = primIMin
_∨_ = primIMax

Π : ∀ {ℓ₁} {ℓ₂} (A : Set ℓ₁) → (A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
Π A P = (x : A) → P x

record Σ {ℓ₁} {ℓ₂} (A : Set ℓ₁) (P : A → Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor _,_
  field
    fst : A
    snd : P fst
open Σ public

postulate
  Path  : ∀ {ℓ} {A : Set ℓ}      → A    → A    → Set ℓ
  PathP : ∀ {ℓ} (P : I → Set ℓ) → P i0 → P i1 → Set ℓ

{-# BUILTIN PATH  Path  #-}
{-# BUILTIN PATHP PathP #-}

-- In cubical TT, equality is internalized via paths
_==_ = Path

module _ {ℓ} {A : Set ℓ} {x : A} where

  refl : x == x
  refl _ = x

  J : ∀ {ℓ'} (P : {y : A} → x == y → Set ℓ') → P refl → {y : A} (p : x == y) → P p
  J P r p = {!!}

  module _ {y : A} (p : x == y) where
    _∙_ : {z : A} → y == z → x == z
    _∙_ q i = primComp (λ _ → A) _ (λ j → λ { (i = i0) → x; (i = i1) → q j }) (p i)

    ! : y == x
    ! i = p (~ i)

ap : ∀ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂}
  (f : A → B) {x y : A} → x == y → f x == f y
ap f {x} = J (λ {y} _ → f x == f y) refl

--coe : ∀ {ℓ} {A B : Set ℓ} → A == B → A → B
--coe {B = B} p a = J (λ _ → B) a p

--transport : ∀ {ℓ₁} {ℓ₂} {A : Set ℓ₁} (P : A → Set ℓ₂) {x y : A} → x == y → P x → P y
--transport P = coe ∘ ap P

contr-singl : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x == y) →
  Path {A = Σ A (λ y → x == y)} (x , refl) (y , p)
contr-singl p i = p i , λ j → p (i ∧ j)

module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} where
  _∼_ : Π A P → Π A P → Set (ℓ₁ ⊔ ℓ₂)
  f ∼ g = (x : A) → f x == g x

  λ= : {f g : Π A P} → f ∼ g → f == g
  λ= p i x = p x i
