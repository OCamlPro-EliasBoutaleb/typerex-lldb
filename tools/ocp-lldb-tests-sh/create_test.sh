#!/bin/bash

# Location of liblldb.so
readonly LLDB_LIB_DIR="/media/jmbto/1decfa63-a052-4827-837e-f93d3d14e9d4/llvm/oml/lib/"

# Location of ocaml compiler suite and related settings/flags
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
create_test ()
{
    local filename=$1
    local name=`basename -s .ml $filename`
    local batch_path="batchs/$name.batch"

    echo Please type some lldb commands and press ctrl-d to finish.

    local input=$(cat)

    echo you wrote
    echo "$input"
    #cat batchs/$name.batch

    read -p "Are you sure? " -n 1 -r
    echo    # (optional) move to a new line
    if [[ ! $REPLY =~ ^[Yy]$ ]]
    then
        exit 1
    fi

    echo "$input" > $batch_path
    local batch_file=`readlink -f $batch_path`

    echo compiling $filename
    compile_and_copy $filename

    local res=$(export LD_LIBRARY_PATH=$LLDB_LIB_DIR;
                $OBUILD_DIR/ocp-lldb.asm -no-auto-start -b $batch_file $WORK_DIR/a.out)
    echo "$res" > prog_refs/$name.ref

    echo base res for $name is
    cat prog_refs/$name.ref
}

main ()
{
    if [[ $# -ne 1 ]]; then
        echo usage : $0 '[OCAML_FILE]'
        exit 1
    fi

    create_test $1
}

main $@
