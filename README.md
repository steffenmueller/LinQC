
# LinQuadChab
(Linear) quadratic Chabauty for integral points on even degree hyperelliptic curves

Code for the algorithms described in ``Linear Quadratic Chabauty'' by Stevan Gajović and Steffen Müller. References below are to this paper.

**Main files**

- *LinQCQ.sage* implements the linear quadratic Chabauty method described in Section 3 for the case of genus 2 curves over the rationals.
- *LinQCRQF.sage* implements the linear quadratic Chabauty method described in Section 4 for the case of genus 2 curves over real quadratic fields.
- *ex1Q.sage* checks the example in §4.4.
- *ex1_qcrqnf.sage* checks the example in §5.3.


**Dependencies**

You need Sage and Magma. Moreover, you need
- the file phts_hyp.sage from [https://github.com/StevanGajovic/heights_above_p](https://github.com/StevanGajovic/heights_above_p);
- Jennifer Balakrishnan's code for even degree Coleman integrals from
from [https://github.com/jbalakrishnan/AWS](https://github.com/jbalakrishnan/AWS). Follow the instructions given there.
- the files *JSearch.m*, *g2-jac.m* and *add.m* from [https://homepages.warwick.ac.uk/staff/S.Siksek/progs/chabnf/](https://homepages.warwick.ac.uk/staff/S.Siksek/progs/chabnf/), due to Samir Siksek. In the file JSearch.m, you need to comment out lines 203 and line 261. 

------------




