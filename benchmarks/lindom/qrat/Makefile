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
QDIR=../../../qrat-trim

GEN=$(NDIR)/gen_lindom.py
SERIALIZE=$(BDIR)/serialize.py
WRAP = $(BDIR)/wrap.py
SOLVE=$(INTERP) $(SDIR)/pgbddq.py
CHECK=$(INTERP) $(WRAP) $(TLIM) $(QDIR)/qrat-trim 


RUN=./gen.sh
GET=$(INTERP) $(NDIR)/grab_data.py

TLIM=7200
VLEVEL=1
N=5
CAT=

all: superclean run

ads: lindom$(CAT)-$(N)-ads.data
adr: lindom$(CAT)-$(N)-adr.data
ar: lindom$(CAT)-$(N)-ar.data
as: lindom$(CAT)-$(N)-as.data

bds: lindom$(CAT)-$(N)-bds.data
bdr: lindom$(CAT)-$(N)-bdr.data
bs: lindom$(CAT)-$(N)-bs.data
br: lindom$(CAT)-$(N)-br.data


lindom$(CAT)-$(N)-ads.data:
	$(GEN) -t a -n $(N) -r lindom$(CAT)-$(N)-ads
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i lindom$(CAT)-$(N)-ads.qcnf \
		-o lindom$(CAT)-$(N)-ads.qrat \
		-p lindom$(CAT)-$(N)-ads.order \
		-L lindom$(CAT)-$(N)-ads.data
	$(CHECK) lindom$(CAT)-$(N)-ads.qcnf lindom$(CAT)-$(N)-ads.qrat -S | tee -a lindom$(CAT)-$(N)-ads.data

lindom$(CAT)-$(N)-adr.data:
	$(GEN) -t a -n $(N) -r lindom$(CAT)-$(N)-adr
	$(SERIALIZE) -a -i lindom$(CAT)-$(N)-adr.qcnf -o lindom$(CAT)-$(N)-adr-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i lindom$(CAT)-$(N)-adr.qcnf \
		-o lindom$(CAT)-$(N)-adr.qrat \
		-p lindom$(CAT)-$(N)-adr.order \
		-L lindom$(CAT)-$(N)-adr.data
	$(CHECK) lindom$(CAT)-$(N)-adr-expand.qcnf lindom$(CAT)-$(N)-adr.qrat | tee -a lindom$(CAT)-$(N)-adr.data

lindom$(CAT)-$(N)-as.data:
	$(GEN) -t a -n $(N) -r lindom$(CAT)-$(N)-as
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i lindom$(CAT)-$(N)-as.qcnf \
		-o lindom$(CAT)-$(N)-as.qrat \
		-p lindom$(CAT)-$(N)-as.order \
		-L lindom$(CAT)-$(N)-as.data
	$(CHECK) lindom$(CAT)-$(N)-as.qcnf lindom$(CAT)-$(N)-as.qrat -S | tee -a lindom$(CAT)-$(N)-as.data

lindom$(CAT)-$(N)-ar.data:
	$(GEN) -t a -n $(N) -r lindom$(CAT)-$(N)-ar
	$(SERIALIZE) -a -i lindom$(CAT)-$(N)-ar.qcnf -o lindom$(CAT)-$(N)-ar-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i lindom$(CAT)-$(N)-ar.qcnf \
		-o lindom$(CAT)-$(N)-ar.qrat \
		-p lindom$(CAT)-$(N)-ar.order \
		-L lindom$(CAT)-$(N)-ar.data
	$(CHECK) lindom$(CAT)-$(N)-ar-expand.qcnf lindom$(CAT)-$(N)-ar.qrat | tee -a lindom$(CAT)-$(N)-ar.data

lindom$(CAT)-$(N)-bds.data:
	$(GEN) -i -t a -n $(N) -r lindom$(CAT)-$(N)-bds
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i lindom$(CAT)-$(N)-bds.qcnf \
		-o lindom$(CAT)-$(N)-bds.qrat \
		-p lindom$(CAT)-$(N)-bds.order \
		-L lindom$(CAT)-$(N)-bds.data
	$(CHECK) lindom$(CAT)-$(N)-bds.qcnf lindom$(CAT)-$(N)-bds.qrat -S | tee -a lindom$(CAT)-$(N)-bds.data

lindom$(CAT)-$(N)-bdr.data:
	$(GEN) -i -t a -n $(N) -r lindom$(CAT)-$(N)-bdr
	$(SERIALIZE) -a -i lindom$(CAT)-$(N)-bdr.qcnf -o lindom$(CAT)-$(N)-bdr-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m d -b \
		-i lindom$(CAT)-$(N)-bdr.qcnf \
		-o lindom$(CAT)-$(N)-bdr.qrat \
		-p lindom$(CAT)-$(N)-bdr.order \
		-L lindom$(CAT)-$(N)-bdr.data
	$(CHECK) lindom$(CAT)-$(N)-bdr-expand.qcnf lindom$(CAT)-$(N)-bdr.qrat | tee -a lindom$(CAT)-$(N)-bdr.data

lindom$(CAT)-$(N)-bs.data:
	$(GEN) -i -t a -n $(N) -r lindom$(CAT)-$(N)-bs
	$(SOLVE) -v $(VLEVEL) -m s -b \
		-i lindom$(CAT)-$(N)-bs.qcnf \
		-o lindom$(CAT)-$(N)-bs.qrat \
		-p lindom$(CAT)-$(N)-bs.order \
		-L lindom$(CAT)-$(N)-bs.data
	$(CHECK) lindom$(CAT)-$(N)-bs.qcnf lindom$(CAT)-$(N)-bs.qrat -S | tee -a lindom$(CAT)-$(N)-bs.data

lindom$(CAT)-$(N)-br.data:
	$(GEN) -i -t a -n $(N) -r lindom$(CAT)-$(N)-br
	$(SERIALIZE) -a -i lindom$(CAT)-$(N)-br.qcnf -o lindom$(CAT)-$(N)-br-expand.qcnf	
	$(SOLVE) -v $(VLEVEL) -m r -b \
		-i lindom$(CAT)-$(N)-br.qcnf \
		-o lindom$(CAT)-$(N)-br.qrat \
		-p lindom$(CAT)-$(N)-br.order \
		-L lindom$(CAT)-$(N)-br.data
	$(CHECK) lindom$(CAT)-$(N)-br-expand.qcnf lindom$(CAT)-$(N)-br.qrat | tee -a lindom$(CAT)-$(N)-br.data

run:
	$(RUN)

data:
	$(GET) *.data


clean:
	rm -f *~ 


superclean: clean
	rm -f *.qcnf *.order *.data *.qrat
