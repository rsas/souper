#!/usr/bin/env python

import fileinput

lines = []
for line in fileinput.input():
    lines.append(line.strip())

res = []
block = []
inblock = False
for line in lines:
    if "cand with constants, constraining wiring" in line:
        inblock = True 
        block.append(line)
    elif "setting input" in line:
        inblock = False
        if len(block):
            res.append(block)
        block = []
    elif inblock:
        block.append(line)

print "Total candidates:", len(res)
dub = {}
for i in res:
    #print "\n".join(i)
    s = "\n".join(i)
    e = dub.get(s)
    assert not e, "%s" % s
    dub[s] = 1

res = []
block = []
inblock = False
for line in lines:
    if "line\tlocations" in line:
        inblock = True 
        block.append(line)
    elif "found valid wiring" in line:
        inblock = False
        if len(block):
            res.append(block)
        block = []
    elif inblock:
        block.append(line)

print "Total line locations:", len(res)
dub = {}
for i in res:
    #print "\n".join(i)
    s = "\n".join(i)
    e = dub.get(s)
    assert not e, "%d\n%s" % (len(dub), s)
    dub[s] = 1

