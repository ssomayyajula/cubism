module Project.Functor where

open import Level using (Lift; lift; suc; _⊔_)
open import Function using (id; const; flip; _∘_; _$_)

open import Data.Product using (_×_)

open import Agda.Builtin.Equality
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat hiding (suc)

record Functor {ℓ} {ℓ'} (F : Set ℓ → Set ℓ') : Set (suc ℓ ⊔ ℓ') where
  infixl 4 _<$>_ _<$_ _$>_
  
  field
    _<$>_ : ∀ {A B} → (A → B) → F A → F B
    <$>-id : ∀ {A} (a : F A) → (id <$> a) ≡ a
    <$>-∘ : ∀ {A B C} (f : B → C) (g : A → B) (x : F A) →
      ((f ∘ g) <$> x) ≡ (f <$> (g <$> x))
  
  _<$_ : ∀ {A B} → A → F B → F A
  x <$ y = const x <$> y
  
  _$>_ : ∀ {A B} → F A → B → F B
  _$>_ = flip (_<$_)
  
  void : ∀ {A} → F A → F (Lift ⊤)
  void = _<$_ (lift tt)

open Functor {{...}} public

record Applicative {ℓ} {ℓ'} (F : Set ℓ → Set ℓ') {{_ : Functor F}} : Set (suc ℓ ⊔ ℓ') where
  infixl 4 _<*>_
  
  field
    pure : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    .<*>-id : ∀ {A} →
      _<*>_ {A} (pure id) ≡ id
    .<*>-∘ : ∀ {A B C} (u : F (A → B)) (v : F (C → A)) (w : F C) →
      (pure (λ f → _∘_ f) <*> u <*> v <*> w) ≡ (u <*> (v <*> w))
    .<*>-hom : ∀ {A B} (f : A → B) (x : A) →
      (pure f <*> pure x) ≡ pure (f x)
    .<*>-inter : ∀ {A B} (u : F (A → B)) (y : A) →
      (u <*> pure y) ≡ (pure (λ f → f y) <*> u)
  
  _*>_ : ∀ {A B} → F A → F B → F B
  u *> v = (id <$ u) <*> v
  
  _<*_ : ∀ {A B} → F A → F B → F A
  _<*_ = flip _*>_
  
open Applicative {{...}} public

record Monad {ℓ} {ℓ'} (F : Set ℓ → Set ℓ') {{_ : Functor F}} {{_ : Applicative F}} : Set (suc ℓ ⊔ ℓ') where
  infixl 1 _>>=_
  
  field
    _>>=_ : ∀ {A B} → F A → (A → F B) → F B
    .pure->>= : ∀ {A B} (a : A) (k : A → F B) → (pure a >>= k) ≡ k a
    .>>=-id : ∀ {A} (m : F A) → (m >>= pure) ≡ m
    .>>=-∘ : ∀ {A B C} (m : F A) (k : A → F B) (h : B → F C) →
              (m >>= (λ x → k x >>= h)) ≡ ((m >>= k) >>= h)

open Monad {{...}} public  

record MonadTrans {ℓ} (F : Set ℓ → Set ℓ) {{_ : Functor F}} {{_ : Applicative F}} {{FM : Monad F}} : Set (suc ℓ) where
  field
    mlift : ∀ {M : Set ℓ → Set ℓ} {A} {{_ : Functor M}} {{_ : Applicative M}} {{_ : Monad M}} →
      M A → F (M A)
    --mlift-pure : ∀ {A} (a : A) → {!!}
    

instance 
  IdentityFunctor : ∀ {ℓ} → Functor {ℓ} id
  IdentityFunctor = record { _<$>_ = _$_ ; <$>-id = λ _ → refl ; <$>-∘ = λ _ _ _ → refl }

  IdentityApplicative : ∀ {ℓ} → Applicative {ℓ} id
  IdentityApplicative = record
                          { pure = id
                          ; _<*>_ = id
                          ; <*>-id = refl
                          ; <*>-∘ = λ _ _ _ → refl
                          ; <*>-hom = λ _ _ → refl
                          ; <*>-inter = λ _ _ → refl
                          }

  IdentityMonad : ∀ {ℓ} → Monad {ℓ} id
  IdentityMonad = record
                    { _>>=_ = λ x f → f x
                    ; pure->>= = λ _ _ → refl
                    ; >>=-id = λ _ → refl
                    ; >>=-∘ = λ _ _ _ → refl
                    }

  IdentityMonadTrans : ∀ {ℓ} → MonadTrans {ℓ} id
  IdentityMonadTrans = record { mlift = id }

{-
WriterT : ∀ {ℓ₁} {ℓ₂} {ℓ₃} (W : Set ℓ₁) (M : Set (ℓ₁ ⊔ ℓ₂) → Set ℓ₃) (A : Set ℓ₂) → Set ℓ₃
WriterT W M A = M (A × W)

Counting : ∀ {ℓ₁} {ℓ₂} {ℓ₃} (M : Set ℓ₁ → Set ℓ₂) (A : Set ℓ₃) → Set ℓ₃
Counting = WriterT Nat
-}

