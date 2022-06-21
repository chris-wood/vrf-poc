SAGEFILES := $(basename $(notdir $(wildcard *.sage)))
PYFILES := $(addprefix sagelib/, $(addsuffix .py,$(SAGEFILES)))
.PRECIOUS: $(PYFILES)

.PHONY: pyfiles
pyfiles: sagelib/__init__.py $(PYFILES)

sagelib/__init__.py:
	mkdir -p sagelib
	echo pass > sagelib/__init__.py

sagelib/%.py: %.sage
	@echo "Parsing $<"
	@sage --preparse $<
	@mv $<.py $@

test: pyfiles
	sage vrf.sage

.PHONY: clean
clean:
	rm -rf sagelib *.pyc *.sage.py *.log __pycache__

setup:
	git submodule update --remote
	cp h2c/poc/*.sage h2c/poc/*.py .