#!/usr/bin/perl -w
# DIMACS to SMT
# Morgan Deters
# Copyright (c) 2009, 2010, 2011  The CVC4 Project

use strict;

my ($nvars, $nclauses);
while(<>) {
    next if /^c/;

    if(/^p\s+cnf\s+(\d+)\s+(\d+)/) {
        ($nvars, $nclauses) = ($1, $2);
        print "(benchmark b\n";
        print ":status unknown\n";
        print ":logic QF_UF \n";
        for(my $i = 1; $i <= $nvars; ++$i) {
            print ":extrapreds ((x$i))\n";
        }
        next;
    }

    chomp;
    @_ = split();
    if ($#_ > 0) {
      print ":assumption";
      if ($#_  >= 1) { print " (or"; }
      for(my $i = 0; $i <= $#_; ++$i) {
        if($_[$i] < 0) {
            print " (not x" . -$_[$i] . ")";
        } 
        if($_[$i] > 0) {
            print " x" . $_[$i];
        }
      }
      if ($#_ >= 1) { print ")"; }
      print "\n";
    }
}

print ":formula true\n";
print ")\n";
