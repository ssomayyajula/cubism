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
open import Agda.Primitive.Cubical public renaming
  (primINeg   to  ~_;
   primIMax   to _∨_;
   primIMin   to _∧_;
   primComp   to comp;
   isOneEmpty to [])

\end{code}}

Now, fix a countable set of names $N$. We obtain a \emph{homotopical} (that is, considering only the boundary elements) notion of $I$ via the \emph{set} \D{I} defined by the following grammar and quotiented by the aforementioned properties. Note that the inclusion of only $\Con{i0}$ and $\Con{i1}$ does not allow us to prove $(\F{\sim}~\Arg{r})~\F{\land}~\Arg{r}=\Con{i0}$ or $(1-\Arg{r})\lor\Arg{r}=\Con{i1}$---\D{I} is faithful to the original definition of $I$.

$$r,s:=\Con{i0}\,\mid\,\Con{i1}\,\mid\,i\in N\,\mid\,\F{\sim}\Arg{r}\,\mid\,\Arg{r}~\F{\land}~\Arg{s}\,\mid\,\Arg{r}~\F{\lor}~\Arg{s}$$

Note that CuTT defines \D{I} as a set, as opposed to a type, for technical reasons TODO CITE. Now, consider that topological paths over a space $A$ are defined as continuous functions from the $I$ to $A$. We may recover a similar definition in CuTT via the \emph{type} \Path. However, we cannot define $\Path:=\D{I}\to\D{A}$ directly since \D{I} is not a type. Once again though, we are only concerned with the ``boundary behavior'' of a topological path $f$---the elements $f(0)$ and $f(1)$. As a result, we define a type $\Path~\Arg{t}~\Arg{u}$ to be the type of paths between endpoints $\Arg{t},\Arg{u}:\D{A}$. As a result, one may introduce a \emph{path abstraction} $\lambda~i\to e:\Path~e[\Con{i0}/i]~e[\Con{i1}/i]$ where $i\in N$. Path abstractions and applications have the expected judgmental equalities with respect to lambda abstractions and applications, except our attention is restricted to \D{I}.

\AgdaHide{
\begin{code}
postulate
  Path  : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
  PathP : ∀ {ℓ} (P : I → Set ℓ) → P i0 → P i1 → Set ℓ

{-# BUILTIN PATH  Path #-}
{-# BUILTIN PATHP PathP #-}

{-Path : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ
Path {A = A} = PathP (λ _ → A)-}
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
  p ∙ q = λ i → comp (λ _ → A) _ (λ { j (i = i0) → x;
                                      j (i = i1) → q j}) (p i)
\end{code}
\end{proof}

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
\caption{Coercion}
\label{fig:coe}
\end{figure}

\begin{code}
module _ {ℓ} {A B : Set ℓ} where
  coe : Path A B → A → B
  coe p x = comp (λ i → p i) _ (λ _ → []) x

open import Function using (_∘_)

module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} where
  transport : (P : A → Set ℓ₂) {x y : A} → Path x y → P x → P y
  transport P = coe ∘ ap P
\end{code}

\subsection{Modeling Equality}

Equality is generally reflexive and substitutive. Theorems: it is an equivalence relation.

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
\end{code}

We can model equality in this type theory via topological paths---continuous functions from the unit interval into a space.

\begin{code}
open import Data.Product

isContr : ∀ {ℓ} → Set ℓ → Set ℓ
isContr A = ∃ λ x → ∀ (y : A) → Path x y

singl : ∀ {ℓ} {A : Set ℓ} → A → Set ℓ
singl a = ∃ λ x → Path a x

module _ {ℓ} {A : Set ℓ} {x y : A} where
  singlIsContr : isContr (singl x)
  singlIsContr = (x , idp) , λ { (_ , p) i → p i , λ j → p (i ∧ j) }

module _ {ℓ₁} {ℓ₂} {A : Set ℓ₁} {x : A} where
  J : (P : ∀ y → Path x y → Set ℓ₂) (r : P x idp) {y : A} (p : Path x y) → P y p
  J P r {y} p = coe (λ i → uncurry P (proj₂ (singlIsContr {y = y}) (y , p) i)) r

postulate
  Id : ∀ {ℓ} {A : Set ℓ} → A → A → Set ℓ

{-# BUILTIN ID    Id   #-}

infixr 30 _≡_
_≡_ = Id

{-# BUILTIN CONID conid #-}

module _ {ℓ} {A : Set ℓ} {x : A} where
  refl : x ≡ x
  refl = conid i1 λ _ → x

-- CHANGED PATH' to PATH
primitive
  primPathApply  : ∀ {ℓ} {A :     Set ℓ} {x y} → Path   x y →      I →  A
  primPathPApply : ∀ {ℓ} {A : I → Set ℓ} {x y} → PathP A x y → (i : I) → A i
  primDepIMin : _
  primIdFace : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → I

module PrimId where
  primitive
    primIdPath : ∀ {ℓ} {A : Set ℓ} {x y : A} → Id x y → Path x y
    primIdJ : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {x : A}
              (P : ∀ y → Id x y → Set ℓ₂) →
              P x refl → ∀ {y} (p : x ≡ y) → P y p

open PrimId renaming (primIdJ to IdJ; primIdPath to idToPath) public

module _ {ℓ} {A : Set ℓ} {x y : A} where
  ! : x ≡ y → y ≡ x
  ! p = IdJ (λ y _ → y ≡ x) refl p

module _ {ℓ} {A : Set ℓ} {x y z : A} where
  infixr 80 _◾_
  _◾_ : x ≡ y → y ≡ z → x ≡ z
  _◾_ p = IdJ (λ y _ → x ≡ y) p



module _ {ℓ} {A : Set ℓ} {x y : A} where
  ◾-unitr : (p : x ≡ y) → p ◾ refl ≡ p
  ◾-unitr _ = refl

  ∙-unitr : (p : Path x y) → Path (p ∙ idp) p
  ∙-unitr p = idp

module _ {ℓ} {A : Set ℓ} {x y z w : A} where
  ∙-assoc : (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → p ◾ (q ◾ r) ≡ (p ◾ q) ◾ r
  ∙-assoc =
    IdJ (λ _ p → ∀ q r → p ◾ (q ◾ r) ≡ (p ◾ q) ◾ r)
      (IdJ (λ _ q → ∀ r → refl ◾ (q ◾ r) ≡ (refl ◾ q) ◾ r)
        (IdJ (λ _ r → refl ◾ (refl ◾ r) ≡ (refl ◾ refl) ◾ r) refl))

\end{code}


\begin{code}
open import Algebra using (Group)

π1 : ∀ {ℓ} → (A : Set ℓ) → A → Group ℓ ℓ
π1 A a = record
  { Carrier = Path a a
  ; _≈_ = _≡_
  ; _∙_ = _∙_
  ; ε = idp
  ; _⁻¹ = _⁻¹
  ; isGroup = record
    { isMonoid = record
      { isSemigroup = record
        { isEquivalence = {!!} --PathIsEquivalence
        ; assoc = {!!}
        ; ∙-cong = {!!}
        }
      ; identity = (λ x → {!!}) , {!!}
      }
    ; inverse = {!!}
    ; ⁻¹-cong = {!!}
    }
  }

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

module RecS¹ {ℓ} (Y : Set ℓ)
             (base* : Y)
             (loop* : Path base* base*) where
  postulate
    f : S¹ → Y
    base-β : f base ↦ base*
  {-# REWRITE base-β #-}

  postulate
    loop-β : Path (ap f loop) loop*

recS¹ = RecS¹.f


open import Agda.Builtin.Int



\end{code}

\subsection{Glueing and Univalence, Almost}

\end{document}
