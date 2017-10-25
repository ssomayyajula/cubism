{-# OPTIONS --cubical #-}

module Cubical where

open import Agda.Primitive
open import Agda.Primitive.Cubical public

open import Function
open import Data.Product

infix 30 ~
~ = primINeg

infixr 20 _∧_ _∨_
_∧_ = primIMin
_∨_ = primIMax

Π : ∀ {ℓ₁} {ℓ₂} (A : Set ℓ₁) → (A → Set ℓ₂) → Set (ℓ₁ ⊔ ℓ₂)
Π A P = (x : A) → P x

postulate
  PathP : ∀ {ℓ} (P : I → Set ℓ) → P i0 → P i1 → Set ℓ
{-# BUILTIN PATHP PathP #-}

_==_ : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
_==_ {A = A} = PathP (λ _ → A)

-- TODO: Homotopy n-types

data ℕ₋₂ : Set where
  ⟨-2⟩ : ℕ₋₂
  S   : ℕ₋₂ → ℕ₋₂

isContr : ∀ {ℓ} → Set ℓ → Set ℓ
isContr A = Σ A (λ x → (y : A) → x == y)

hasLevel : ℕ₋₂ → ∀ {ℓ} → Set ℓ → Set ℓ
hasLevel ⟨-2⟩ A = isContr A
hasLevel (S n) A = (x y : A) → hasLevel n (x == y)

module _ {ℓ} {A : Set ℓ} {x : A} where
  -- 3.1
  refl : x == x
  refl _ = x

  -- 3.2.3
  isContr-Singleton-lem : {y : A} (p : x == y) → (x , refl) == (y , p)
  isContr-Singleton-lem p i = p i , λ j → p (i ∧ j)

transp : {ℓ : I → Level} (P : (i : I) → Set (ℓ i)) → P i0 → P i1
transp P ai0 = primComp P i0 (λ x → isOneEmpty) ai0

module _ {ℓ} {A : Set ℓ} {x : A} where
  J : ∀ {ℓ'} (P : (y : A) → x == y → Set ℓ') → P x refl → {y : A} (p : x == y) → P y p
  J P r p = transp (λ i → uncurry P $ isContr-Singleton-lem p i) r

  module _ {y : A} (p : x == y) where
    ! : y == x
    ! = J (λ y _ → y == x) refl p
    
    _∙_ : {z : A} → y == z → x == z
    _∙_ {z} = J (λ y _ → y == z → x == z) id p

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} where
  module _ {B : Set ℓ₂} (f : A → B) where
    -- 3.2.1
    ap : {x y : A} → x == y → f x == f y
    ap {x} = J (λ y _ → f x == f y) refl

    fiber : (y : B) → Set (ℓ₁ ⊔ ℓ₂)
    fiber y = Σ A (λ x → y == f x)

  coe : {B : Set ℓ₁} → A == B → A → B
  coe p = J (λ B _ → A → B) id p
  
  module _  {P : A → Set ℓ₂} where
    infix 4 _∼_
    _∼_ : Π A P → Π A P → Set (ℓ₁ ⊔ ℓ₂)
    f ∼ g = (x : A) → f x == g x
    
    -- 3.2.2
    λ= : {f g : Π A P} → f ∼ g → f == g
    λ= p i x = p x i

isEquiv : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) → (A → B) → Set (ℓ₁ ⊔ ℓ₂)
isEquiv _ B f = (y : B) → isContr (fiber f y)

{-# BUILTIN ISEQUIV isEquiv #-}

primitive
  primGlue : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) (φ : I)
    → (T : Partial (Set ℓ₂) φ) → (f : PartialP φ (λ o → T o → A))
    → (pf : PartialP φ (λ o → isEquiv (T o) A (f o))) → Set ℓ₂

module _ {ℓ₁ ℓ₂} {A : Set ℓ₁} where
  transport : (P : A → Set ℓ₂) {x y : A} → x == y → P x → P y
  transport P = coe {ℓ₂} {ℓ₁} ∘ ap P

infix 4 _≃_
_≃_ : ∀ {ℓ₁ ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set (ℓ₁ ⊔ ℓ₂)
A ≃ B = Σ (A → B) (isEquiv A B)

ide : ∀ {ℓ} {A : Set ℓ} → A ≃ A
ide = id , λ y → (y , refl) , isContr-Singleton-lem ∘ proj₂

glue = primGlue

Glue : ∀ {ℓ₁ ℓ₂} (A : Set ℓ₁) → (φ : I) → (T : Partial (Set ℓ₂) φ)
  (f : (PartialP φ (λ o → T o ≃ A))) → Set ℓ₂
Glue A φ T f = glue A φ T (λ o → proj₁ $ f o) (λ o → proj₂ $ f o)

-- For some reason, the deMorgan algebra laws do not hold judgmentally...
ua : ∀ {ℓ} {A B : Set ℓ} → A ≃ B → A == B
ua {A = A} {B} f i = Glue B (~ i ∨ i)
  (λ {(i = i0) → A ; (i = i1) → B})
  (λ {(i = i0) → f ; (i = i1) → ide})

open import Data.Bool

record qinv {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
  constructor iso
  field
    g : B → A
    ε : g ∘ f ∼ id
    η : f ∘ g ∼ id

-- isoToEquiv in cubicaltt
qinv-isEquiv : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) → qinv f → isEquiv A B f
qinv-isEquiv f (iso g ε η) y = (g y , ! (η y)) , {!!}

invol-isEquiv :  ∀ {ℓ₁} {A : Set ℓ₁} (f : A → A) → f ∘ f ∼ id → isEquiv A A f
invol-isEquiv f h = qinv-isEquiv f (iso f h h)

notP : Bool == Bool
notP = ua $ not , invol-isEquiv not λ { true → refl; false → refl }

-- Actually computes!!!
-- Sort of, Agda crashes because of the hole above but I verified it in Saizan's demo
not-ua : Bool → Bool
not-ua = coe {lzero} {lzero} notP

id-ua : Bool → Bool
id-ua = coe {lzero} {lzero} $ ua $ id , {!!}
