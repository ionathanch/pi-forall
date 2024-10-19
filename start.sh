#!/bin/sh

set -u

QEMU_ACCEL=tcg

case $(uname -m) in
  'x86_64')
    case $(uname) in
      'Darwin')
        QEMU_ACCEL=hvf
        ;;
      'Linux')
        QEMU_ACCEL=kvm
        ;;
      *)
        ;;
    esac
    ;;
  *)
  ;;
esac

qemu-system-x86_64 \
  -m     2048 \
  -accel ${QEMU_ACCEL} \
  -cpu   host \
  -nic   user \
  -hda   disk.qcow2
  "$@"