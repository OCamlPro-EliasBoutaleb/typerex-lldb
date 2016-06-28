#!/bin/bash

#set -x

. assert.sh

_clean() {
    _assert_reset # reset state
    DEBUG= STOP= INVARIANT=1 DISCOVERONLY= CONTINUE= # reset flags
    eval $* # read new flags
}

readonly LLDB_LIB_DIR="/media/jmbto/1decfa63-a052-4827-837e-f93d3d14e9d4/llvm/oml/lib/"
readonly OCAML_DIR="/home/jmbto/ocpwork/typerex-private/ocaml/4.02.1+ocp1"
readonly OCAMLOPT="$OCAML_DIR/ocamlopt"
readonly OCAMLOPT_FLAGS="-I stdlib -g -S -dvb"
readonly OBUILD_DIR="/home/jmbto/ocpwork/typerex-private/_obuild/ocp-lldb/"

readonly PROG_DIR=$(readlink -m $(dirname $0))
readonly TESTS_DIR="$PROG_DIR/tests"
readonly WORK_DIR="/tmp"

compile_and_copy ()
{
    local target=`readlink -f $1`

    rm $WORK_DIR/a.out

    (
    cd $OCAML_DIR &&
    ./ocamlopt $OCAMLOPT_FLAGS $target -o $WORK_DIR/a.out
    )

    test -e $WORK_DIR/a.out
}

run_batch_and_cmp ()
{
    local batch_file=`readlink -f $1`
    local name=`basename -s .batch $batch_file`
    local ref_file="$name.ref"
    
    colordiff $ref_file \
        <(
        export LD_LIBRARY_PATH=$LLDB_LIB_DIR;
        cd $OBUILD_DIR &&
        ./ocp-lldb.asm -no-auto-start -b $batch_file $WORK_DIR/a.out
        )
}

main_run_test_suite ()
{
    # Create a tempfile containing the LLDB script we want to execute on startup
    readonly TMPFILE=$(mktemp /tmp/ocp-lldb-commands.XXXXXX)

    # Make sure to delete the tempfile no matter what
    trap "rm -f $TMPFILE; exit" INT TERM EXIT

    compile_and_copy "rec_fn.ml" && run_batch_and_cmp "rec_fn.batch"

    #assert_raises "compile_and_copy rec_fn.ml"
    #assert_raises "run_batch_and_cmp rec_fn.batch"

    assert_end demo
}

main_run_test_suite

