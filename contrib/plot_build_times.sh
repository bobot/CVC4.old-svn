#!/bin/bash

times=$1
echo "Analyzing $times"

total_time=0
start_time=

function BUILD {

case $1 in 
START*)
  start_time=`date --utc --date "$2 $3" +%s`
  ;;
END*)
  end_time=`date --utc --date "$2 $3" +%s`
  compile_time=$((end_time-start_time))
  echo $start_time $compile_time
  total_time=$((total_time+compile_time))
  ;;
esac
}

source "$times"

echo "Total compile time: $total_time s"
