# Stratified Type Theory

This repository contains the supplementary material for
Stratified Type Theory (StraTT), consisting of three parts:

* `coq/`: A Coq development of the syntactic metatheory of StraTT.
* `agda/`: An Agda mechanization of the consistency of subStraTT.
* `impl/`: A Haskell implementation of a type checker for StraTT augmented with datatypes,
  based on [pi-forall](https://github.com/sweirich/pi-forall).

Detailed descriptions of their contents and of build instructions
are found in the `README.md`s of their respective directories.

## Quickstart

These are brief instructions on how to check the supplementary material,
which have also been packaged up into an artifact at [TODO].
The artifact is a QEMU virtual machine image with only necessary prerequisites installed,
and is approximately 2 GB, but may grow up to 12 GB if modified
(say, by installing GHC).
The virtual machine may use up to 2 GB of memory only following these instructions.
The instructions are also labelled with "[Artifact only]" if using the VM,
and "[No artifact]" if running locally,
which assumes that Coq, Agda, and GHCup are installed.

0. [Artifact only] Install [QEMU](https://www.qemu.org/download/)
1. [Artifact only] Run the script `./start.sh`;
   alternatively, you can run the QEMU command directly:
   ```sh
   qemu-system-x86_64 -m 2048 -accel <accel> -cpu host -nic user -hda disk.qcow2
   ```
   * Linux:     use `kvm`  for `<accel>`
   * Apple:     use `hvf`  for `<accel>`
   * Windows:   use `whpx` for `<accel>`
   * Otherwise: use `tcg`  for `<accel>`
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
   2. [No artifact] Build implementation
      (will increase total disk size to ~8.2 GB):
      1. `ghcup install ghc 9.6.6` to install GHC
      2. `stack install` to recompile implementation
   3. `stratt pi/StraTT.pi` to check examples listed in paper
   4. `stratt pi/README.pi` to check all examples provided
7. [Artifact only] All changes made can be undone by `git reset && git restore .`

## Artifact troubleshooting

The [Arch Linux wiki on QEMU](https://wiki.archlinux.org/title/QEMU)
has good guidance on using QEMU if problems persist.
Flags can be passed directly to the `start.sh` script.

* If there is an "invalid accelerator" error, use `tcg` for `<accel>`
* If more memory is required, increase the number of MB in `-m 2048`
* If things aren't displaying correctly, add the `-nographic` flag
  to see the output directly in the terminal

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
3. If any partition modifications need to be done:
   ```sh
   modprobe nbd max_part=4
   qemu-nbd -c /dev/nbd0 disk.qcow2
   # inspect/mount/modify/etc. device
   qemu-nbd -d /dev/nbd0
   ```
4. Shrink disk to occupied space only:
   ```sh
   virt-sparsify --in-p lace disk.qcow2
   mv disk.qcow2 disk-old.qcow2
   qemu-img convert -O qcow2 disk-old.qcow2 disk.qcow2
   rm disk-old.qcow2
   ```