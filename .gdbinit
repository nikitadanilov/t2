set height 0
set confirm off
set print thread-events off
set print inferior-events off
handle SIGSEGV noprint nostop pass
break immanentise
command
set scheduler-locking on
end

define nrec
  set $i = 0
  set $n = ((struct node *)$arg0)
  while $i < (1 << NREC_SHIFT)
    set $pos = ($n->hand + $i) & NREC_MASK
    if $i == 0
      set $delta = 0
    else
      set $delta = $n->nrec[$pos].time - $n->nrec[($pos - 1) & NREC_MASK].time
    end
    printf "%2i %12lu %12lu %10x %6i %c\n", $i, $n->nrec[$pos].time, $delta, $n->nrec[$pos].thread, $n->nrec[$pos].seq, $n->nrec[$pos].op
    set $i = $i + 1
  end
end
