set height 0
set confirm off
set print thread-events off
set print inferior-events off
handle SIGSEGV noprint nostop pass
break immanentise

