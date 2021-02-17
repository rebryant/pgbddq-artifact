INTERP=python3
# Abbreviations:
# Players
#   a, b
# Proof types
#   d: Dual
#   r: Refutation
#   s: Satisfaction


NDIR=..
BDIR=../..
SDIR=../../../solver

GEN=$(NDIR)/gen_lindom.py
SOLVE=$(INTERP) $(SDIR)/pgbddq.py
CHECK=$(INTERP) $(SDIR)/qchecker.py

RUN=./gen.sh
GET=$(INTERP) $(NDIR)/grab_data.py

VLEVEL=2
N=5
CAT=

all: superclean run

as: lindom$(CAT)-$(N)-as.data
ar: lindom$(CAT)-$(N)-ar.data
ad: lindom$(CAT)-$(N)-ad.data

bs: lindom$(CAT)-$(N)-bs.data
br: lindom$(CAT)-$(N)-br.data
bd: lindom$(CAT)-$(N)-bd.data

lindom$(CAT)-$(N)-ad.data:
	$(GEN) -t a -n $(N) -r lindom$(CAT)-$(N)-ad
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i lindom$(CAT)-$(N)-ad.qcnf \
		-o lindom$(CAT)-$(N)-ad.qproof \
		-p lindom$(CAT)-$(N)-ad.order \
		-L lindom$(CAT)-$(N)-ad.data
	$(CHECK) -m d -i lindom$(CAT)-$(N)-ad.qcnf -p lindom$(CAT)-$(N)-ad.qproof | tee -a lindom$(CAT)-$(N)-ad.data

lindom$(CAT)-$(N)-as.data:
	$(GEN) -t a -n $(N) -r lindom$(CAT)-$(N)-as
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i lindom$(CAT)-$(N)-as.qcnf \
		-o lindom$(CAT)-$(N)-as.qproof \
		-p lindom$(CAT)-$(N)-as.order \
		-L lindom$(CAT)-$(N)-as.data
	$(CHECK) -m s -i lindom$(CAT)-$(N)-as.qcnf -p lindom$(CAT)-$(N)-as.qproof | tee -a lindom$(CAT)-$(N)-as.data

lindom$(CAT)-$(N)-ar.data:
	$(GEN) -t a -n $(N) -r lindom$(CAT)-$(N)-ar
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i lindom$(CAT)-$(N)-ar.qcnf \
		-o lindom$(CAT)-$(N)-ar.qproof \
		-p lindom$(CAT)-$(N)-ar.order \
		-L lindom$(CAT)-$(N)-ar.data
	$(CHECK) -m r -i lindom$(CAT)-$(N)-ar.qcnf -p lindom$(CAT)-$(N)-ar.qproof | tee -a lindom$(CAT)-$(N)-ar.data

lindom$(CAT)-$(N)-bd.data:
	$(GEN) -t a -i -n $(N) -r lindom$(CAT)-$(N)-bd
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i lindom$(CAT)-$(N)-bd.qcnf \
		-o lindom$(CAT)-$(N)-bd.qproof \
		-p lindom$(CAT)-$(N)-bd.order \
		-L lindom$(CAT)-$(N)-bd.data
	$(CHECK) -m d -i lindom$(CAT)-$(N)-bd.qcnf -p lindom$(CAT)-$(N)-bd.qproof | tee -a lindom$(CAT)-$(N)-bd.data

lindom$(CAT)-$(N)-bs.data:
	$(GEN) -t a -i -n $(N) -r lindom$(CAT)-$(N)-bs
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i lindom$(CAT)-$(N)-bs.qcnf \
		-o lindom$(CAT)-$(N)-bs.qproof \
		-p lindom$(CAT)-$(N)-bs.order \
		-L lindom$(CAT)-$(N)-bs.data
	$(CHECK) -m s -i lindom$(CAT)-$(N)-bs.qcnf -p lindom$(CAT)-$(N)-bs.qproof | tee -a lindom$(CAT)-$(N)-bs.data

lindom$(CAT)-$(N)-br.data:
	$(GEN) -t a -i -n $(N) -r lindom$(CAT)-$(N)-br
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i lindom$(CAT)-$(N)-br.qcnf \
		-o lindom$(CAT)-$(N)-br.qproof \
		-p lindom$(CAT)-$(N)-br.order \
		-L lindom$(CAT)-$(N)-br.data
	$(CHECK) -m r -i lindom$(CAT)-$(N)-br.qcnf -p lindom$(CAT)-$(N)-br.qproof | tee -a lindom$(CAT)-$(N)-br.data

run:
	$(RUN)

data:
	$(GET) *.data


clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qproof
