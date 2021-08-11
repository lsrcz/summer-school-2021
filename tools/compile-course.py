#!/usr/bin/python3

import collections
import glob
import os
import re
import shutil

script_dir = os.path.dirname(__file__)
instructor_dir = os.path.relpath(os.path.join(script_dir, ".."))
print(f"instructor_dir  {instructor_dir}")
student_dir = os.path.relpath(os.path.join(instructor_dir, "../summer-school-2021/"))
print(f"student_dir  {student_dir}")

def gather_elements():
  elements = collections.defaultdict(lambda: collections.defaultdict(set))
  for path in glob.glob(instructor_dir+"/chapter*/*/*"):
    postfix = path[len(instructor_dir)+1:]
    (chapter,type,filename) = postfix.split("/")
    #print((chapter,type,filename))
    elements[chapter][type].add(filename)
  return elements

def transform_solution(input_filename, output_filename):
  elide = False
  input_lines = [line.rstrip() for line in open(input_filename).readlines()]
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
  open(output_filename, "w").write(''.join([line+"\n" for line in output_lines]))
  print(f"Generated {output_filename}")

def generate_exercise_from_solution(chapter, type, filename):
  mo = re.compile("exercise(\d+)_solution.dfy").search(filename)
  if mo:
    num = mo.groups()[0]
    print(f"Transform {num}")
    transform_solution(
      os.path.join(instructor_dir, chapter, type, filename),
      os.path.join(student_dir, chapter, "exercises", f"exercise{num}.dfy"))
  else:
    print(f"Copy {filename}")

def process_elements():
  elements = gather_elements()
  for chapter in sorted(elements.keys()):
    output_chapter = os.path.join(student_dir, chapter)

    # Destroy existing data
    #print(output_chapter)
    shutil.rmtree(output_chapter)
    os.mkdir(output_chapter)

    for type in sorted(elements[chapter].keys()):
      print(f"# chapter {chapter} type {type}")
      if type != "solutions":
        for filename in sorted(elements[chapter][type]):
          print(type, filename)
          try:
            os.makedirs(os.path.join(student_dir, chapter, type))
          except FileExistsError: pass
          shutil.copyfile(
            os.path.join(instructor_dir, chapter, type, filename),
            os.path.join(student_dir, chapter, type, filename))
      else:
        print(f"solutions in {chapter}")
        for filename in sorted(elements[chapter][type]):
          generate_exercise_from_solution(chapter, type, filename)

process_elements()
