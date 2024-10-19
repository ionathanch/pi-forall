@echo off

set PATH=%PATH%;C:\Program Files\qemu

:: `-accel whpx,kernel-irqchip=off` doesn't work
qemu-system-x86_64^
  -m 2048^
  -accel tcg^
  -cpu max^
  -nic user^
  -hda disk.qcow2