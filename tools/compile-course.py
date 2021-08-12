#!/usr/bin/python3

import collections
import glob
import os
import re
import shutil
import operator
import subprocess
import sys

script_dir = os.path.dirname(__file__)
instructor_dir = os.path.relpath(os.path.join(script_dir, ".."))
print(f"instructor_dir  {instructor_dir}")
student_dir = os.path.relpath(os.path.join(instructor_dir, "../summer-school-2021/"))
print(f"student_dir  {student_dir}")

def mkdirs(dstpath):
  """Make directories to include file dstpath, if necessary"""
  try:
    os.makedirs(os.path.dirname(dstpath))
  except FileExistsError: pass

def mkdir_and_copy(srcpath, dstpath):
  """Copy file from srcpath to dstpath, creating any necessary directories."""
  mkdirs(dstpath)
  shutil.copyfile(srcpath, dstpath)

class Element:
  def __init__(self, chapter, type, filename):
    self.chapter = chapter
    self.type = type
    self.filename = filename

    self.num = None
    if type=="solutions":
      mo = re.compile("exercise(\d+)_solution.dfy").search(filename)
      if mo:
        self.num = mo.groups()[0]
      self.exercise_path = os.path.join(student_dir, self.chapter, "exercises",
        f"exercise{self.num}.dfy" if self.num else self.filename)
    else:
      self.exercise_path = None

  def is_dafny_source(self):
    return self.num != None

  def key(self):
    return (self.chapter, self.type, self.filename)

  def __repr__(self):
    return self.instructor_path()

  def __lt__(self, other):
    return operator.lt(self.key(), other.key())

  def instructor_path(self):
    return os.path.join(instructor_dir, self.chapter, self.type, self.filename)

  def student_path(self):
    return os.path.join(student_dir, self.chapter, self.type, self.filename)

  def transform_solution(self):
    if "elide" in self.filename:
      return
    elide = False
    input_lines = [line.rstrip() for line in open(self.instructor_path()).readlines()]
    output_lines = []
    for input_line in input_lines:
      output_line = input_line
      if input_line.startswith("//#exercise"):
        # exercise substitution
        output_line = input_line[11:]
      elif input_line.startswith("//#elide"):
        # single-line elision
        output_line = None
      elif input_line.startswith("//#start-elide"):
        # multi-line elision
        elide = True
        output_line = None
      elif input_line.startswith("//#end-elide"):
        elide = False
        output_line = None
      elif elide:
        output_line = None
      if output_line!=None:
        output_lines.append(output_line)
    mkdirs(self.exercise_path)
    open(self.exercise_path, "w").write(''.join([line+"\n" for line in output_lines]))
    print(f"Generated {self.exercise_path}")

  def compile(self):
    print(f"-- {self.type}/{self.filename}")
    if self.type == "solutions":
      # solutions map into exercises dir
      print(f"Transform {self.num}")
      self.transform_solution()
    else:
      # everything else goes in the same relative dir
      mkdir_and_copy(self.instructor_path(), self.student_path())

  def test(self):
    if self.is_dafny_source():
      cmd = ["dafny", "/compile:0", "/vcsCores:6", self.instructor_path()]
      print(f"  -- {' '.join(cmd)}")
      return subprocess.call(cmd)==0

class Catalog:
  def __init__(self):
    self.gather_elements()

  def gather_elements(self):
    self.elements = collections.defaultdict(lambda: collections.defaultdict(set))
    for path in glob.glob(instructor_dir+"/chapter*/*/*"):
      postfix = path[len(instructor_dir)+1:]
      element = Element(*postfix.split("/"))
      self.elements[element.chapter][element.type].add(element)

  def foreach_element(self, fun):
    dbg_count = 0
    for chapter in sorted(self.elements.keys()):
      output_chapter = os.path.join(student_dir, chapter)

      # Destroy existing data
      #print(output_chapter)
      try:
        shutil.rmtree(output_chapter)
      except FileNotFoundError: pass
      os.mkdir(output_chapter)

      for type in sorted(self.elements[chapter].keys()):
        print(f"# chapter {chapter} type {type}")
        for element in sorted(self.elements[chapter][type]):
          dbg_count += 1
          #if dbg_count>12: return
          fun(element)

  def compile_elements(self):
    self.foreach_element(lambda elt: elt.compile())

  def test_elements(self):
    results = []
    self.foreach_element(lambda elt: results.append((elt, elt.test())))
    failures = []
    for (elt, result) in results:
      if result==False:
        failures.append(elt)
    if len(failures)==0:
      print("All tests passed")
    else:
      print(f"Failing tests count: {len(failures)}")
      print(failures)

def main():
  action = sys.argv[1] if len(sys.argv)==2 else "compile"
  if action=="compile":
    Catalog().compile_elements()
  else:
    Catalog().test_elements()

main()
