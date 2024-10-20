# Installation

These are instructions on how to install and verify the supplementary material,
either locally or using the paper artifact.
The artifact is a QEMU virtual machine image with only necessary prerequisites installed,
and is approximately 2 GB, but may grow up to 12 GB if modified (say, by installing GHC).
The virtual machine may use up to 2 GB of memory only following these instructions.
The instructions are also labelled with "[Artifact only]" iff using the VM,
and "[No artifact]" iff running locally,
which assumes that Coq, Agda, and GHCup are installed.

0. [Artifact only] Install [QEMU](https://www.qemu.org/download/)
   * On Windows, virtualization needs to be enabled:
     from the Start menu, search for and open Windows Features,
     select Hyper-V and Windows Hypervisor Platform,
     and click OK
1. [Artifact only] Run the script `start.sh` or `start.bat` (Windows),
   which will run the following command:
   ```sh
   qemu-system-x86_64 -m 2048 -accel <accel> -cpu max -nic user -hda disk.qcow2
   ```
   * Linux:   `kvm` for `<accel>`
   * Apple:   `hvf` for `<accel>`
   * Windows: `tcg` for `<accel>`
   * Other:   `tcg` for `<accel>`
2. [Artifact only] Within QEMU, login as `root` (blank password)
   and `cd StraTT` for artifact files
4. To check the Coq development:
   1. `cd coq` from the `StraTT` directory
   2. `make -Bf CoqSrc.mk` to force check proof of type safety
   3. Assumptions (in axioms.v) will be printed by above
5. To check the Agda development:
   1. `cd agda` from the `StraTT` directory
   2. `rm *.agdai` to clean up previously checked files
   3. `agda consistency.agda` to check proof of consistency
   4. `grep "postulate" *.agda` to find postulates
6. To run prototype implementation:
   1. `cd impl` from the `StraTT` directory
   2. [No artifact] Build implementation:
      1. `ghcup install ghc 9.6.6` to install GHC
      2. `stack install` to compile implementation
   3. `stratt pi/StraTT.pi` to check examples listed in paper
   4. `stratt pi/README.pi` to check all examples provided
7. [Artifact only] All changes made can be undone by `git reset && git restore .`

## Artifact troubleshooting

The [Arch Linux wiki on QEMU](https://wiki.archlinux.org/title/QEMU)
has good guidance on using QEMU if problems persist.
Flags can be passed directly to the `start.sh` script.

* If `qemu-system-x86_64` cannot be found,
  ensure that the path to QEMU binaries is in your `PATH` environment variable
* If there is an "invalid accelerator" error, use `tcg` for `<accel>`
* If more memory is required, increase the number of MB in `-m 2048`
* If things aren't displaying correctly, add the `-nographic` flag
  to see the output directly in the terminal

## Expected outputs

The following are the expected outputs from running the commands above
in the corresponding directories in the VM.

```sh
[/root/StraTT/agda] $ agda consistency.agda
Checking consistency (/root/StraTT/agda/consistency.agda).
 Checking common (/root/StraTT/agda/common.agda).
 Checking accessibility (/root/StraTT/agda/accessibility.agda).
 Checking syntactics (/root/StraTT/agda/syntactics.agda).
 Checking reduction (/root/StraTT/agda/reduction.agda).
 Checking typing (/root/StraTT/agda/typing.agda).
 Checking semantics (/root/StraTT/agda/semantics.agda).
 Checking soundness (/root/StraTT/agda/soundness.agda).

[/root/StraTT/agda] $ grep "postulate" *.agda
accessibility.agda:  private postulate

[/root/StraTT/coq] $ make -Bf CoqSrc.mk
COQDEP VFILES
COQC StraTT_ott.v
COQC StraTT_inf.v
COQC axioms.v
COQC tactics.v
COQC basics.v
COQC incr.v
COQC ctx.v
COQC restrict.v
COQC subst.v
COQC inversion.v
COQC typesafety.v
Axioms:
ineq_Type_Bottom : forall S : signature, DEquiv S a_Type a_Bottom -> False
ineq_Pi_Type
  : forall (S : signature) (B1 : tm) (j : Datatypes.nat) (B2 : tm),
    DEquiv S (a_Pi B1 j B2) a_Type -> False
ineq_Pi_Bottom
  : forall (S : signature) (B1 : tm) (j : Datatypes.nat) (B2 : tm),
    DEquiv S (a_Pi B1 j B2) a_Bottom -> False
ineq_Arrow_Type
  : forall (S : signature) (A1 A2 : tm),
    DEquiv S (a_Arrow A1 A2) a_Type -> False
ineq_Arrow_Pi
  : forall (S : signature) (A1 B1 A2 : tm) (j : Datatypes.nat) (B2 : tm),
    DEquiv S (a_Arrow A1 A2) (a_Pi B1 j B2) -> False
ineq_Arrow_Bottom
  : forall (S : signature) (A1 A2 : tm),
    DEquiv S (a_Arrow A1 A2) a_Bottom -> False
Eqdep.Eq_rect_eq.eq_rect_eq
  : forall (U : Type) (p : U) (Q : U -> Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
DEquiv_Pi_inj3
  : forall (S : signature) (A1 B1 : tm) (j1 j2 : Datatypes.nat)
      (A2 B2 a : tm),
    lc_tm a ->
    DEquiv S (a_Pi A1 j1 B1) (a_Pi A2 j2 B2) ->
    DEquiv S (open B1 a) (open B2 a)
DEquiv_Pi_inj2
  : forall (S : signature) (A1 B1 : tm) (j1 j2 : Datatypes.nat) (A2 B2 : tm),
    DEquiv S (a_Pi A1 j1 B1) (a_Pi A2 j2 B2) -> j1 = j2
DEquiv_Pi_inj1
  : forall (S : signature) (A1 B1 : tm) (j1 j2 : Datatypes.nat) (A2 B2 : tm),
    DEquiv S (a_Pi A1 j1 B1) (a_Pi A2 j2 B2) -> DEquiv S A1 A2
DEquiv_Arrow_inj2
  : forall (S : signature) (A1 B1 A2 B2 : tm),
    DEquiv S (a_Arrow A1 B1) (a_Arrow A2 B2) -> DEquiv S B1 B2
DEquiv_Arrow_inj1
  : forall (S : signature) (A1 B1 A2 B2 : tm),
    DEquiv S (a_Arrow A1 B1) (a_Arrow A2 B2) -> DEquiv S A1 A2

[/root/StraTT/impl] $ stratt pi/StraTT.pi
processing StraTT.pi...
Parsing File "pi/StraTT.pi"
type checking...
Checking module "StraTT"
module StraTT where
id' : (X : Type 0) -> (x : X 0) -> X @ 1
id' = \X x. x
id : (X : Type 0) -> X -> X @ 1
id = \X x. x
idid1 : ((X : Type 1) -> X -> X) -> (X : Type 0) -> X -> X @ 2
idid1 = \id. id ((X : Type 0) -> X -> X) (\X. id X)
idid2 : ((X : Type 2) -> X -> X) -> (X : Type 0) -> X -> X @ 3
idid2 = \id.
          id (((X : Type 1) -> X -> X) -> (X : Type 0) -> X -> X) idid1 (\X.
                                                                           id X)
idid3 : ((X : Type 3) -> X -> X) -> (X : Type 0) -> X -> X @ 4
idid3 = \id.
          id (((X : Type 2) -> X -> X) -> (X : Type 0) -> X -> X) idid2 (\X.
                                                                           id X)
idid1id : ((idid1 (\X x. x)) = (\X x. x)) @ 2
idid1id = Refl
idid2id : ((idid2 (\X x. x)) = (\X x. x)) @ 3
idid2id = Refl
idid3id : ((idid3 (\X x. x)) = (\X x. x)) @ 4
idid3id = Refl
OptionC : Type -> Type @ 1
OptionC = \X. (Y : Type 0) -> Y -> (X -> Y) -> Y
NoneC : (X : Type 0) -> OptionC X @ 1
NoneC = \X Y y f. y
SomeC : (X : Type 0) -> X -> OptionC X @ 1
SomeC = \X x Y y f. f x
joinC : (X : Type 0) -> OptionC (OptionC X) -> OptionC X @ 1
joinC = \X oopt Y y f. oopt Y y (\opt. opt Y y f)
Option' : (X : Type 0) -> Type @ 2
Option' = \X.
            (Y : Type 0) -> (_ : Y 0) -> (_1 : (_2 : X 0) -> Y 1) -> Y
None' : (X : Type 0) -> Option' X @ 2
None' = \X Y y f. y
Some' : (X : Type 0) -> (_ : X 0) -> Option' X @ 2
Some' = \X x Y y f. f x
join' : (X : Type 0) -> (_ : Option'^2 (Option' X) 4) -> Option' X @ 5
join' = \X oopt Y y f. oopt Y y (\opt. opt Y y f)
neg : Type -> Type @ 0
neg = \X. X -> Void
DecC : Type -> Type @ 1
DecC = \X. (Z : Type 0) -> (X -> Z) -> (neg X -> Z) -> Z
yes : (X : Type 0) -> X -> DecC X @ 1
yes = \X x Z f g. f x
no : (X : Type 0) -> neg X -> DecC X @ 1
no = \X nx Z f g. g nx
neg' : (_ : Type 0) -> Type @ 1
neg' = \X. X -> Void
DecC' : (_ : Type 0) -> Type @ 3
DecC' = \X.
          (Z : Type 0) -> (yz : (x : X 0) -> Z 2) -> (nz : (nx : neg' X 1) -> Z 2) -> Z
yes' : (X : Type 0) -> (x : X 0) -> DecC' X @ 3
yes' = \X x Z f g. f x
no' : (X : Type 0) -> (nx : neg' X 1) -> DecC' X @ 3
no' = \X nx Z f g. g nx
eq : (X : Type 0) -> X -> X -> Type @ 1
eq = \X x y. (P : X -> Type 0) -> P x -> P y
refl : (X : Type 0) -> (x : X 0) -> eq X x x @ 1
refl = \X x P px. px
isProp : (X : Type 0) -> Type @ 1
isProp = \X. (x : X 0) -> (y : X 0) -> eq X x y
isSet : (X : Type 0) -> Type @ 2
isSet = \X. (x : X 0) -> (y : X 0) -> isProp^1 (eq X x y)
data Dec (X : Type) : Type 0 where
  Yes of (_689 : X) @ 0
  No of (_691 : neg X) @ 0
decDNE : (X : Type 0) -> Dec X -> neg (neg X) -> X @ 1
decDNE = \X dec nnx.
           case dec of
             Yes x -> x
             No nx -> absurd nnx nx
data Eq (X : Type @ 0) (x : X) (y : X) : Type 1 where
  refl of (z : X @ 0) (z = x) (z = y) @ 1
isProp' : (X : Type 0) -> Type @ 1
isProp' = \X. (x : X 0) -> (y : X 0) -> Eq X x y
isSet' : (X : Type 0) -> Type @ 2
isSet' = \X. (x : X 0) -> (y : X 0) -> isProp'^1 (Eq X x y)
UIP : (X : Type 0) -> (x : X 0) -> (p : Eq X x x 1) -> Eq^1 (Eq X x x) p (refl x) @ 2
UIP = \X x p.
        case p of
          refl z -> refl^1 (refl z)
data NPair (X : Type @ 0) (P : X -> Type) : Type 1 where
  MkPair of (x : X @ 0) (_814 : P x) @ 1
nfst : (X : Type 0) -> (P : X -> Type 0) -> NPair X P -> X @ 1
nfst = \X P p.
         case p of
           MkPair x y -> x
nsnd : (X : Type 0) -> (P : X -> Type 0) -> (p : NPair X P 1) -> P (nfst X P p) @ 2
nsnd = \X P p.
         case p of
           MkPair x y -> y
data DPair (X : Type @ 0) (P : (_ : X 0) -> Type) : Type 1 where
  MkPair of (x : X @ 0) (_865 : P x) @ 1
dfst : (X : Type 0) -> (P : (_ : X 0) -> Type 1) -> DPair X P -> X @ 2
dfst = \X P p.
         case p of
           MkPair x y -> x
dsnd : (X : Type 0) -> (P : (_ : X 0) -> Type 1) -> (p : DPair X P 1) -> case p of
                                                                           MkPair x y -> P x @ 2
dsnd = \X P p.
         case p of
           MkPair x y -> y
data U : Type 1 where MkU of (X : Type @ 0) (_923 : X -> U) @ 1
data WF (u : U) : Type 2 where
  MkWF of (X : Type @ 0)
          (f : X -> U @ 1)
          (_933 : (x : X 1) -> WF (f x))
          (u = MkU X f) @ 2
wf : (u : U 1) -> WF u @ 2
wf = \u.
       case u of
         MkU X f -> MkWF X f (\x. wf (f x))
loop : U @ 1
loop = TRUSTME
nwfLoop : WF loop -> Void @ 2
nwfLoop = \wfLoop. TRUSTME
falseLoop : Void @ 2
falseLoop = nwfLoop (wf loop)
regular : U -> Type @ 1
regular = \u.
            case u of
              MkU X f -> (x : X 0) -> ((f x) = (MkU X f)) -> Void
R : U^2 @ 3
R = MkU^2 (NPair^1 U regular) (\ureg. TRUSTME)
R_nonreg : regular^2 R -> Void @ 3
R_nonreg = TRUSTME
R_reg : regular^2 R @ 3
R_reg = \ureg p.
          case ureg of
            MkPair u reg -> TRUSTME
falseR : Void @ 3
falseR = R_nonreg R_reg
P : Type -> Type @ 0
P = \X. X -> Type
UU : Type @ 1
UU = (X : Type 0) -> (P (P X) -> X) -> P (P X)
tau : P (P UU) -> UU @ 1
tau = \t X f p. t (\s. p (f (s X f)))
sig : UU^1 -> P (P UU) @ 2
sig = \s. s UU tau
Delta : P UU^1 @ 2
Delta = \y. ((p : P UU 1) -> sig y p -> p (tau (sig y))) -> Void
Omega : UU @ 3
Omega = tau (\p. (x : UU^1 2) -> sig x p -> p (\X. x X))
M : (x : UU^2 3) -> sig^1 x Delta -> Delta^1 x @ 4
M = \x s d. d Delta s (\p. d (\y. p (tau (sig y))))
D : Type @ 3
D = (p : P UU 1) -> ((x : UU 1) -> sig TRUSTME p -> p x) -> p Omega
```

## Artifact creation

This section is **not** for artifact reviewers;
it contains notes on how the artifact itself was created.

1. Create 12 GB dynamic disk image:
   `qemu-img create -f qcow2 disk.qcow2 12G`
2. Boot disk with Alpine Linux (virtual) 3.20.3 for installation:
   ```sh
   qemu-system-x86_64 -m 2048 -accel kvm -cpu host -nic user -nographic \
      -hda disk.qcow2 -cdrom "alpine-virt-3.20.3-x86_64" -boot order=d
   ```
3. Boot image using `start` script and install prerequisite software:
   ```sh
   apk add binutils-gold coq curl gcc g++ git gmp-dev libc-dev libffi-dev make musl-dev ncurses-dev opam perl tar xz z3 zlib-dev
   ```
   then install GHCup, Cabal, Stack, GHC, Agda, and Metalib as required
4. If any partition modifications need to be done:
   ```sh
   modprobe nbd max_part=4
   qemu-nbd -c /dev/nbd0 disk.qcow2
   # inspect/mount/modify/etc. device
   qemu-nbd -d /dev/nbd0
   ```
5. Shrink disk to occupied space only:
   ```sh
   virt-sparsify --in-p lace disk.qcow2
   mv disk.qcow2 disk-old.qcow2
   qemu-img convert -O qcow2 disk-old.qcow2 disk.qcow2
   rm disk-old.qcow2
   ```