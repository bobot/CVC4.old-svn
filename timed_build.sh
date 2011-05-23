#!/bin/bash
date +"BUILD START: %F %T" >> build_times.log
make $@
date +"BUILD END: %F %T" >> build_times.log

