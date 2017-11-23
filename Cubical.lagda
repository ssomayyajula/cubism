\documentclass[letterpaper]{article}

% Language
\usepackage[english]{babel}

% Set margins
\usepackage[margin=1in]{geometry}
\usepackage{float}

% Math
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{amsthm}

% Links
\usepackage{hyperref}

\usepackage{tikz}

% Enable Literate Agda
\usepackage[references,links]{agda}

% Set Sans font for Agda code
\setsansfont[Scale=MatchLowercase]{DejaVuSansMono.ttf}

% Environments & Commands
\newcommand{\D}{\AgdaDatatype}
\newcommand{\F}{\AgdaFunction}
\newcommand{\Arg}{\AgdaArgument}
\newcommand{\Con}{\AgdaInductiveConstructor}

\newcommand{\removelinebreaks}[1]{
  \begingroup\def\\{ }#1\endgroup}

\newtheorem{theorem}{Theorem}[section]
\newcommand{\Path}{\D{Path}}
\newcommand{\comp}{\F{comp}}

\newcommand{\drawpath}[4]{
  \node at (0,0) (#2) {\Arg{#2}};
  \node at (#4,0) (#3) {\Arg{#3}};
  \draw[->] (#2) -- node[above] {\Arg{#1}} (#3);
}

\title{Excursions in Cubical Type Theory}
\author{Siva Somayyajula}

\begin{document}
\maketitle

\section{Motivation}

In recent years, the \emph{univalent foundations} program has aimed to develop a foundations of constructive mathematics with an enriched notion of equality. Technicality aside, recall that your average intensional type theory may only express intensional equalities between mathematical objects. Unlike extensional type theories, they may not express, for example, the extensional equality of functions. However, an intensional type theory with the \emph{univalence axiom} may identify equivalent types as equal for an approriate definition of equivalence. Consequently, function extensionality becomes a theorem in this system, and many results that require a coarser notion of equality become provable. As some folks at the Type Theory Podcast say, "in a sense, [this] is more extensional than extensional type theory," because the range of expressible equalities (based on the behavior of objects) is widened. In fact, univalence is expressly \emph{inconsistent} with extensional type theory, so it seems that an intensional and univalent type theory poses many benefits over existing systems.

\emph{Homotopy type theory} (HoTT), the first such type theory developed by this program, extends Martin-L\"of type theory with the univalence axiom and other constructs to develop synthetic proofs of results in homotopy theory. Indeed, given our above exposition, HoTT seems to be the type theory to end all type theories. However, its critical weakness is that univalence lacks a computation rule. This is not an issue for those who intend to leverage HoTT for proofs, but what of programmers? There are many situations where one may want to use univalence to seamlessly switch between different views of the same abstract type when writing a software application. While these programs would enjoy various type safety guarantees in HoTT, they would also just get \emph{stuck}. Enter \emph{cubical type theory} (CuTT), which is advertised as providing a ``constructive interpretation of the univalence axiom;'' that is, univalence gets a computation rule. We will give a brief introduction to CubicalTT and demonstrate its power and computational benefits in a variety of case studies motivated by concerns in software engineering, all in Agda.

\section{Cubical Type Theory}

CuTT starts with intuitionistic type theory and then introduces a set of primitive types that ultimately capture the topological notion of an $n$-dimensional cube. We will begin with the type of \emph{intervals}.

\subsection{Intervals and Paths}

Consider the unit interval $I=[0,1]$ and some basic facts about it. In particular, $I$ is bounded by least and greatest elements $0$ and $1$, respectively. We also have trivial equalities $1-0=1$ and $1-1=0$. Perhaps more interestingly, for all $r,s\in I$:

\begin{align*}
1-\max(r,s)&=\min(1-r,1-s)\\
1-\min(r,s)&=\max(1-r,1-s)
\end{align*}

Together, these properties make $(I, \max, \min, 0, 1)$ a bounded distributive lattice and $r\mapsto 1-r$ a De Morgan involution. In other words, $(I, \max, \min, 0, 1, r\mapsto 1-r)$ is a De Morgan algebra. Thus, it is appropriate to refer to $\max$ as $\lor$, $\min$ as $\land$, and $r\mapsto 1-r$ as $\sim$.

\AgdaHide{
\begin{code}
{-# OPTIONS --cubical --rewriting #-}

module _ where

open import Agda.Primitive using (Level)
open import Function using (id)

module Primitives where
  open import Agda.Primitive.Cubical public renaming
    (primINeg   to  ~_;
     primIMax   to _∨_;
     primIMin   to _∧_;
     primComp   to comp;
     isOneEmpty to [])

module Unsafe' (dummy : Set₁) = Primitives
unsafeComp = Unsafe'.comp Set
unsafePOr = Unsafe'.primPOr Set

open Primitives public

\end{code}}

Now, fix a countable set of names $N$. We obtain a \emph{homotopical} (that is, considering only the boundary elements) notion of $I$ via the \emph{set} \D{I} defined by the following grammar and quotiented by the aforementioned properties. Note that the inclusion of only $\Con{i0}$ and $\Con{i1}$ does not allow us to prove $(\F{\sim}~\Arg{r})~\F{\land}~\Arg{r}=\Con{i0}$ or $(1-\Arg{r})\lor\Arg{r}=\Con{i1}$---\D{I} is faithful to the original definition of $I$.

$$r,s:=\Con{i0}\,\mid\,\Con{i1}\,\mid\,i\in N\,\mid\,\F{\sim}\Arg{r}\,\mid\,\Arg{r}~\F{\land}~\Arg{s}\,\mid\,\Arg{r}~\F{\lor}~\Arg{s}$$

Note that CuTT defines \D{I} as a set, as opposed to a type, for technical reasons TODO CITE. Now, consider that topological paths over a space $A$ are defined as continuous functions from the $I$ to $A$. We may recover a similar definition in CuTT via the \emph{type} \Path. However, we cannot define $\Path:=\D{I}\to\D{A}$ directly since \D{I} is not a type. Once again though, we are only concerned with the ``boundary behavior'' of a topological path $f$---the elements $f(0)$ and $f(1)$. As a result, we define a type $\Path~\Arg{t}~\Arg{u}$ to be the type of paths between endpoints $\Arg{t},\Arg{u}:\D{A}$. As a result, one may introduce a \emph{path abstraction} $\lambda~i\to e:\Path~e[\Con{i0}/i]~e[\Con{i1}/i]$ where $i\in N$. Path abstractions and applications have the expected judgmental equalities with respect to lambda abstractions and applications, except our attention is restricted to \D{I}.

\AgdaHide{
\begin{code}
postulate
  PathP : ∀ {ℓ} (P : I → Set ℓ) → P i0 → P i1 → Set ℓ


  

{-# BUILTIN PATHP PathP #-}

Path : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
Path {A = A} = PathP (λ _ → A)

\end{code}}

Perhaps that after dealing with this level of abstraction (pun intended), we deserve a few examples where we reason about the basic properties of paths.

\AgdaNoSpaceAroundCode{
\begin{theorem}[Constant path]
If $\Arg{x}:A$, we have
\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} {x : A} where
\end{code}}
\begin{code}
  idp : Path x x
\end{code}
\end{theorem}
\begin{proof}
We want a path abstraction that is invariant on an element in \D{I}, so
\begin{code}
  idp _ = x
\end{code}
\end{proof}

\begin{theorem}[Path inversion]
\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} {x y : A} where
  infix 120 _⁻¹
\end{code}}
\begin{code}
  _⁻¹ : Path x y → Path y x
\end{code}
\end{theorem}
\begin{proof}
Given a path $\Arg{p}$ from $\Arg{x}$ to $\Arg{y}$, $\Arg{p}~(\F{\sim}~\Con{i0})=\Arg{p}~\Con{i1}=\Arg{y}$ and $\Arg{p}~(\F{\sim}~\Con{i1})=\Arg{p}~\Con{i0}=\Arg{x}$, so:
\begin{code}
  p ⁻¹ = λ i → p (~ i)
\end{code}
\end{proof}

\begin{theorem}[Action on paths]
If $\Arg{f}:\D{A}\to\D{B}$ and $\Arg{x},\Arg{y}:\D{A}$, we have
\AgdaHide{
\begin{code}
module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {x y : A} where
\end{code}}
\begin{center}
\begin{code}
  ap : Path x y → Path (f x) (f y)
\end{code}
\end{center}
\end{theorem}
\begin{proof}
Given a path \Arg{p} from \Arg{x} to \Arg{y}, $\Arg{f}~(\Arg{p}~\Con{i0})=\Arg{f}~\Arg{x}$ and $\Arg{f}~(\Arg{p}~\Con{i1})=\Arg{f}~\Arg{y}$, so:
\begin{code}
  ap p i = f (p i)
\end{code}
\end{proof}
}

Paths look suspiciously like the identity type---in particular, these examples correspond to reflexivity and function substitutivity, respectively. Indeed, we will see how we may leverage paths to represent equalities; but first, we will see why CuTT is cubical. If $P_n$ is a type family parameterized by $n$ intervals, it induces the an $n$-dimensional cube; see figure TODO in TODO. The manipulation of paths and cubes will lead to primitive operations that allow us to do mathematics and programming.

\subsection{Kan compositions}
Let \tikz[baseline]{\drawpath{p~i}{x}{y}{1}} denote $\Arg{p}:\Path~\Arg{x}~\Arg{y}$ applied to an element \Arg{i} of \D{I}. Now, consider the diagram in figure \ref{fig:comppaths}.

\begin{figure}[H]
\centering
\begin{tikzpicture}[->]
  \node at (0,0) (x1) {\Arg{x}};
  \node at (0,3) (x2) {\Arg{x}};
  \node at (3,0) (y)  {\Arg{y}};
  \node at (3,3) (z)  {\Arg{z}};

  \path
    (x1) edge         node[left]  {x}         (x2)
    (x2) edge[dashed] node[above] {?}         (z)
    (x1) edge         node[below] {\Arg{p~i}} (y)
    (y)  edge         node[right] {\Arg{q~j}} (z);
\end{tikzpicture}
\caption{Composition of paths}
\label{fig:comppaths}
\end{figure}

We would like to compute the composition of these paths by ``completing'' the square. It turns out that completing cubes is ubiquitous in CuTT, but we currently do not have an operation that lets us do that. As a result, CuTT adds \comp, which fills in the missing face of a partially specified cube by taking the following arguments. 

\begin{enumerate}
\item A type family \Arg{P} parameterized by an interval
\item An element of the interval (this is due to a limitation in Agda and is irrelevant in proper implementations of CuTT)
\item A partial specification of a cube that introduces a fresh element \Arg{j} of \D{I} to describe its faces (of type \Arg{P~j})
\item The bottom face of said cube (of type \Arg{P}~\Con{i0})
\end{enumerate}

\subsection{Modeling Equality}

Equality is substitutive. Theorems: it is an equivalence relation.

\begin{code}
module _ {ℓ} {A B : Set ℓ} where
  coe : Path A B → A → B
  coe p x = comp (λ i → p i) _ (λ _ → []) x

fill : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → (φ : I) →
  ((i : I) → Partial (A i) φ) → A i0 → (i : I) → A i
fill A φ u a0 i = unsafeComp (λ j → A (i ∧ j)) (φ ∨ ~ i)
  (λ j → unsafePOr φ (~ i) (u (i ∧ j)) λ { (i = i0) → a0 }) a0

module _ {ℓ} {A : Set ℓ} where
  coe-β : (x : A) → Path x (coe idp x)
  coe-β x = {!!}
  
  {-open import Agda.Primitive using (Level)
  coed : {ℓ : I → Agda.Primitive.Level} → (A : (i : I) → Set (ℓ i)) → A i0 → A i1
  coed A x = comp A i0 (λ _ → []) x-}

open import Function using (_∘_)

module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} where
  transport : (P : A → Set ℓ₂) {x y : A} → Path x y → P x → P y
  transport P = coe ∘ ap P

  transport⁻¹ : (P : A → Set ℓ₂) {x y : A} → Path x y → P y → P x
  transport⁻¹ P = transport P ∘ _⁻¹

module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} where
  transport-β : (P : A → Set ℓ₂) {x : A} (ux : P x) → Path ux (transport P idp ux)
  transport-β P {x} ux = {!!}
\end{code}

We can model equality in this type theory via topological paths---continuous functions from the unit interval into a space.

\begin{code}
open import Data.Product

isContr : ∀ {ℓ} → Set ℓ → Set ℓ
isContr A = ∃ λ x → ∀ (y : A) → Path x y

singl : ∀ {ℓ} {A : Set ℓ} → A → Set ℓ
singl a = ∃ λ x → Path a x

module _ {ℓ} {A : Set ℓ} {x : A} where
  singlIsContr : isContr (singl x)
  singlIsContr = (x , idp) , λ { (_ , p) i → p i , λ j → p (i ∧ j) }

module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {x : A} where
  J : (P : ∀ y → Path x y → Set ℓ₂) (r : P x idp) {y : A} (p : Path x y) → P y p
  J P r {y} p = transport (uncurry P) (proj₂ singlIsContr (y , p)) r

module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {x : A} where
  J-β : (P : ∀ y → Path x y → Set ℓ₂) (r : P x idp) → Path (J P r idp) r
  J-β P = {!!} --transport-β (uncurry P) --coe-β
\end{code}

\begin{theorem}[Composition of paths]
\AgdaHide{
\begin{code}
module _ {ℓ} {A : Set ℓ} {x y z : A} where
  infixr 80 _∙_
\end{code}}
\begin{code}
  _∙_ : Path x y → Path y z → Path x z
\end{code}
\end{theorem}
\begin{proof}
\begin{code}
  _∙_ = J (λ y _ → Path y z → Path x z) id
\end{code}
\end{proof}

\begin{code}
open import Relation.Binary using (IsEquivalence; Setoid)

PathIsEquivalence : ∀ {ℓ} {A : Set ℓ} → IsEquivalence (Path {A = A})
PathIsEquivalence = record
  { refl = idp
  ; sym = _⁻¹
  ; trans = _∙_ }

PathSetoid : ∀ {ℓ} → Set ℓ → Setoid ℓ ℓ
PathSetoid A = record
  { Carrier = A
  ; _≈_ = Path
  ; isEquivalence = PathIsEquivalence
  }

module _ {ℓ} {A : Set ℓ} where
  open import Relation.Binary.EqReasoning (PathSetoid A) public

_≡_ = Path
\end{code}

\begin{code}

module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} where
  _∼_ : (f g : (x : A) → P x) → Set _
  f ∼ g = (x : A) → f x ≡ g x

  module _ {f g : (x : A) → P x} where
    app≡ : f ≡ g → f ∼ g
    app≡ p x i = p i x

    λ≡ : f ∼ g → f ≡ g
    λ≡ h i x = h x i
\end{code}

\begin{code}
module _ {ℓ} {A : Set ℓ} {x y : A} where
  ∙-unitl : (p : Path x y) → idp ∙ p ≡ p
  ∙-unitl = app≡ (J-β (λ y _ → Path x y → Path x y) _)

module _ {ℓ} {A : Set ℓ} {x y : A} where
  ∙-unitr : (p : Path x y) → p ∙ idp ≡ p
  ∙-unitr = J (λ _ p → p ∙ idp ≡ p) (∙-unitl idp)

  ∙-invl : (p : Path x y) → p ⁻¹ ∙ p ≡ idp
  ∙-invl = J (λ _ p → p ⁻¹ ∙ p ≡ idp) (∙-unitl idp)

  ∙-invr : (p : Path x y) → p ∙ p ⁻¹ ≡ idp
  ∙-invr = J (λ _ p → p ∙ p ⁻¹ ≡ idp) (∙-unitl idp)

module _ {ℓ} {A : Set ℓ} {x y z w : A} where 
  ∙-assoc : (p : Path x y) (q : Path y z) (r : Path z w) → (p ∙ q) ∙ r ≡ p ∙ q ∙ r
  ∙-assoc = J (λ _ p → ∀ q r → (p ∙ q) ∙ r ≡ p ∙ q ∙ r)
    λ q r → ap (λ x → x ∙ r) (∙-unitl q) ∙ ∙-unitl (q ∙ r) ⁻¹

open import Algebra using (Group)

Ω[_,_] : ∀ {ℓ} (A : Set ℓ) → A → Set ℓ 
Ω[ _ , a ] = Path a a

{-Ω-Group : ∀ {ℓ} (A : Set ℓ) → A → Group ℓ ℓ
Ω-Group A x = record
  { Carrier = Ω[ A , x ]
  ; _≈_ = _≡_
  ; _∙_ = _∙_
  ; ε = idp
  ; _⁻¹ = _⁻¹
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isEquivalence = PathIsEquivalence
        ; assoc = ∙-assoc
        ; ∙-cong = {!!} }
      ; identity = ∙-unitl , ∙-unitr }
    ; inverse = ∙-invl , ∙-invr
    ; ⁻¹-cong = {!!}
    }
  }-}

fiber : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) (y : B) → Set _
fiber {A = A} f y = Σ[ x ∈ A ] y ≡ f x

module _ {ℓ₁} {ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) where
  isEquiv : (A → B) → Set _
  isEquiv f = (y : B) → isContr (fiber f y)

{-# BUILTIN ISEQUIV isEquiv #-}

infix 4 _≃_
_≃_ : ∀ {ℓ₁} {ℓ₂} → Set ℓ₁ → Set ℓ₂ → Set _
A ≃ B = Σ (A → B) (isEquiv _ _)

module _ {ℓ} {A : Set ℓ} where
  contr : isContr A → (φ : I) → (u : Partial A φ) → A
  contr (c , p) φ u = comp (λ _ → A) φ (λ i o → p (u o) i) c

module _ {ℓ₁} {ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) where
  module _ (f : A ≃ B) (φ : I) (t : Partial A φ) (a : B {- [ φ ↦ f t ] -})
           (p : PartialP φ (λ o → a ≡ proj₁ f (t o))) where
    equiv : fiber (proj₁ f) a -- [ φ ↦ (t , λ j → a) ]
    equiv = contr ((proj₂ f) a) φ (λ o → t o , (λ i → p o i))

ide : ∀ {ℓ} {A : Set ℓ} → A ≃ A
ide = id , λ y → singlIsContr {x = y}

module _ {ℓ} {A B : Set ℓ} where
  pathToEquiv : A ≡ B → A ≃ B
  pathToEquiv = J (λ B _ → A ≃ B) ide

{-pathToEquivProof : ∀ {ℓ} (E : I → Set ℓ) → isEquiv (E i0) (E i1) (coed E)
pathToEquivProof E = proj₂ (pathToEquiv P)
  where P : E i0 ≡ E i1
        P i = E i

{-# BUILTIN PATHTOEQUIV pathToEquivProof #-}-}

module _ {ℓ ℓ' : I → Level} {T : ∀ i → Set (ℓ i)} {A : ∀ i → Set (ℓ' i)}
         (f : ∀ i → T i → A i) (φ : I) (t : ∀ i → Partial (T i) φ)
         (t0 : T i0 {- [ φ ↦ t i0 ] -}) where
  private
    c1 c2 : A i1
    c1 = unsafeComp A φ (λ i → (λ { (φ = i1) → f i (t i itIsOne)})) (f i0 t0)
    c2 = f i1 (unsafeComp T φ t t0)

    a0 = f i0 t0

    a : ∀ i → Partial (A i) φ
    a i = (λ { (φ = i1) → f i ((t i) itIsOne)})

    u : ∀ i → A i
    u = fill A φ a a0

    v : ∀ i → T i
    v = fill T φ t t0

  pres : c1 ≡ c2
  pres j = unsafeComp A (φ ∨ (j ∨ ~ j)) (λ i → primPOr φ (j ∨ ~ j)
    (a i) \ { (j = i1) → f i (v i); (j = i0) → u i}) a0

module GluePrims where
  primitive
    primGlue    : ∀ {ℓ ℓ'} (A : Set ℓ) (φ : I)
      → (T : Partial (Set ℓ') φ) → (f : PartialP φ (λ o → T o → A))
      → (pf : PartialP φ (λ o → isEquiv (T o) A (f o))) → Set ℓ'
    prim^glue   : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {f : PartialP φ (λ o → T o → A)}
      → {pf : PartialP φ (λ o → isEquiv (T o) A (f o))}
      → PartialP φ T → A → primGlue A φ T f pf
    prim^unglue : ∀ {ℓ ℓ'} {A : Set ℓ} {φ : I}
      → {T : Partial (Set ℓ') φ} → {f : PartialP φ (λ o → T o → A)}
      → {pf : PartialP φ (λ o → isEquiv (T o) A (f o))}
      → primGlue A φ T f pf → A

open GluePrims public renaming (prim^glue to glue ; prim^unglue to unglue)

Glue : ∀ {ℓ ℓ'} (A : Set ℓ) → (φ : I) → (T : Partial (Set ℓ') φ)
  (f : (PartialP φ (λ o → T o ≃ A))) → Set ℓ'
Glue A φ T f = primGlue A φ T (λ o → proj₁ (f o)) (λ o → proj₂ (f o))

-- TODO: Need unsafeComp and unsafePOr

module Unsafe'' (dummy : Set1) = GluePrims
module Unsafe''' = Unsafe'' Set

unsafeGlue = Unsafe'''.prim^glue

primitive
  primFaceForall : (I → I) → I

module FaceForall (φ : I → I) where
  δ = primFaceForall φ
  postulate
    ∀v : ∀ i → IsOne (φ i) → IsOne ((δ ∨ (φ i0 ∧ ~ i)) ∨ (φ i1 ∧ i))
    ∀e : IsOne δ → ∀ i → IsOne (φ i)

module _ {ℓ ℓ'} {A : Set ℓ} {φ : I} {T : Partial (Set ℓ') φ}
           {f : (PartialP φ λ o → T o ≃ A)} where
  fwdGlueIso : PartialP φ (λ o → Glue A φ T f → T o)
  fwdGlueIso (φ = i1) = id

  backGlueIso : PartialP φ (λ o → T o → Glue A φ T f)
  backGlueIso (φ = i1) = id

  lemGlueIso : (b : PartialP φ (λ _ → Glue A φ T f)) → PartialP φ λ o →
                 (unglue {φ = φ} (b o)) ≡ (proj₁ (f o) (fwdGlueIso o (b o)))
  lemGlueIso _ (φ = i1) = idp

module CompGlue {ℓ ℓ' : I → Level} (A : ∀ i → Set (ℓ i))
                (φ : I → I) (T : ∀ i → Partial (Set (ℓ' i)) (φ i))
                (f : ∀ i → PartialP (φ i) λ o → T i o ≃ A i)
                where
  B : ∀ i → Set (ℓ' i)
  B = λ i → Glue (A i) (φ i) (T i) (f i)

  module Local (ψ : I) (b : ∀ i → Partial (B i) ψ)
               (b0 : B i0 {- [ ψ ↦ b i0 ] -}) where
    a : ∀ i → Partial (A i) ψ
    a i = λ o → unglue {φ = φ i} (b i o)

    module Forall (δ : I) (∀e : IsOne δ → ∀ i → IsOne (φ i)) where
      a0 : A i0
      a0 = unglue {φ = φ i0} b0

      a1' = unsafeComp A ψ a a0

      t1' : PartialP δ (λ o → T i1 (∀e o i1))
      t1' o = unsafeComp (λ i → T i (∀e o i)) ψ
                (λ i o' → fwdGlueIso {φ = φ i} (∀e o i) (b i o'))
                (fwdGlueIso {φ = φ i0} (∀e o i0) b0)

      ω : PartialP δ _
      ω o = pres (λ i → proj₁ (f i (∀e o i))) ψ
              (λ i x → fwdGlueIso {φ = φ i} (∀e o i) (b i x))
              (fwdGlueIso {φ = φ i0} (∀e o i0) b0)

      a1'' = unsafeComp (λ _ → A i1) (δ ∨ ψ)
              (λ j → unsafePOr δ ψ (λ o → ω o j) (a i1)) a1'

      g : PartialP (φ i1) _
      g o = (equiv (T i1 _) (A i1) (f i1 o) (δ ∨ ψ)
        (unsafePOr δ ψ t1' (λ o' → fwdGlueIso {φ = φ i1} o (b i1 o'))) a1''
        ((unsafePOr δ ψ (λ {(δ = i1) → idp})
          ((λ{ (ψ = i1) → lemGlueIso {φ = φ i1} (λ _ → b i1 itIsOne) o })))))
      t1 α : PartialP (φ i1) _
      t1 o = proj₁ (g o)
      α o = proj₂ (g o)

      a1 = unsafeComp (λ j → A i1) (φ i1 ∨ ψ)
             (λ j → unsafePOr (φ i1) ψ (λ o → α o j) (a i1)) a1''

      b1 : Glue _ (φ i1) (T i1) (f i1)
      b1 = unsafeGlue {φ = φ i1} t1 a1
    b1 = Forall.b1 (FaceForall.δ φ) (FaceForall.∀e φ)

compGlue : {ℓ ℓ' : I → Level} (A : ∀ i → Set (ℓ i)) (φ : I → I)
           (T : ∀ i → Partial (Set (ℓ' i)) (φ i))
           (f : ∀ i → PartialP (φ i) λ o → (T i o) → (A i)) →
           (pf : ∀ i → PartialP (φ i) (λ o → isEquiv (T i o) (A i) (f i o))) →
           let B : ∀ i → Set (ℓ' i)
               B = λ i → primGlue (A i) (φ i) (T i) (f i) (pf i)
           in  (ψ : I) (b : ∀ i → Partial (B i) ψ) (b0 : B i0) → B i1
compGlue A φ T f pf ψ b b0 =
  CompGlue.Local.b1 A φ T (λ i p → (f i p) , (pf i p)) ψ b b0

{-# BUILTIN COMPGLUE compGlue #-}

module _ {ℓ} {A B : Set ℓ} where
  ua : A ≃ B → A ≡ B
  ua e i = Glue B _ (λ { (i = i0) → A; (i = i1) → B})
    λ { (i = i0) → e; (i = i1) → ide }

open import Data.Bool

-- Axiom: pathToEquiv is an equivalence with ua as its inverse
-- TODO: ua-β

\end{code}

\begin{code}
module RewriteRelation where

module _ {ℓ} {X : Set ℓ} where
  infix 30 _↦_
  postulate 
    _↦_ : X → X → Set ℓ
{-# BUILTIN REWRITE _↦_ #-}

postulate
  S¹ : Set
  base : S¹
  loop : Path base base

module RecS¹ {ℓ} {Y : Set ℓ}
             (base* : Y)
             (loop* : Path base* base*) where
  postulate
    f : S¹ → Y
    base-β : f base ↦ base*
  {-# REWRITE base-β #-}

  postulate
    loop-β : Path (ap f loop) loop*

recS¹ = RecS¹.f


open import Data.Integer
open import Data.Nat

-- Wind a path n times
loop^ : ℤ → Ω[ S¹ , base ]
loop^ (+ 0)        = idp
loop^ (+ suc n)    = loop ∙ loop^ (+ n)
loop^ -[1+ 0 ]     = loop ⁻¹
loop^ -[1+ suc n ] = loop ⁻¹ ∙ loop^ -[1+ n ]

-- Universal cover of circle
{-Cover : S¹ → Set
Cover = recS¹ ℤ {!!}

windFrom : ℤ → Ω[S¹] → ℤ
windFrom n p = transport Cover p n

encode : ∀ {a} → Path base a → Cover a
encode = J (λ a _ → Cover a) (+ 0)

-- Winding number of path
windingNum : Ω[S¹] → ℤ
windingNum p = transport Cover p (+ 0)-}

--suc≃ : ℤ ≃ ℤ


\end{code}

\subsection{Glueing and Univalence, Almost}

\end{document}
