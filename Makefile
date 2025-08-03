COQMODULE    := Ordinal
COQTHEORIES  := \
	src/*.v \

.PHONY: all theories clean

all: build

build: Makefile.coq
	$(MAKE) -f Makefile.coq all

quick: Makefile.coq
	$(MAKE) -f Makefile.coq vio

# Add "-deprecated-from-Coq" to _CoqProject to silence warnings.
# Remove it when droping support for Coq <= 8.20.
Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-Q src $(COQMODULE)"; \
   \
   echo "-arg -w -arg -deprecated-from-Coq"; \
   \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f _CoqProject Makefile.coq Makefile.coq.conf
