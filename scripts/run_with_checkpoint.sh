#!/bin/bash
function run_with_checkpoint() {
    target_start=$1
    target_end=$2
    gen_mode=$3
    timeout=$4
    total_num=116000 

    mkdir -p /path2output/outputs_${target_start}_${target_end}
    touch /path2output/outputs_${target_start}_${target_end}/checkpoint.txt
    touch /path2output/outputs_${target_start}_${target_end}/local_checkpoint.txt
    echo 10 > /path2output/outputs_${target_start}_${target_end}/checkpoint.txt  #any number except 0
    echo 0 > /path2output/outputs_${target_start}_${target_end}/local_checkpoint.txt # start from 0
    num_python_runs=0
    while true
    do 
        remain_num=$(cat /path2output/outputs_${target_start}_${target_end}/checkpoint.txt)
        start_idx=$(cat /path2output/outputs_${target_start}_${target_end}/local_checkpoint.txt)
        if [ "$remain_num" -eq 0 ] 
        then
            break
        fi
        num_python_runs=$((num_python_runs+1))
        if [ "$num_python_runs" -gt 1 ]
        then
            start_idx=$((start_idx+10000))
            echo $start_idx > /path2output/outputs_${target_start}_${target_end}/local_checkpoint.txt
        fi

        if [ "$start_idx" -gt "$total_num" ]  # for the last 10000, just drop it and reset the local_checkpoint 
        then
            echo 0 > /path2output/outputs_${target_start}_${target_end}/local_checkpoint.txt
            start_idx=0
        fi
        python data_generator.py  \
            --with_checkpoint \
            --checkpoint_interval 10000 \
            --start $start_idx \
            --target_start $target_start \
            --target_end $target_end\
            --gen_mode $gen_mode\
            --hard_timeout $timeout
    done
}

run_with_checkpoint $1 $2 $3 $4