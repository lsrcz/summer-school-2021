#!/usr/bin/python3

import collections
import glob
import os
import shutil

script_dir = os.path.dirname(__file__)
instructor_dir = os.path.relpath(os.path.join(script_dir, ".."))
print(f"instructor_dir  {instructor_dir}")
student_dir = os.path.relpath(os.path.join(instructor_dir, "../summer-school-2021/"))
print(f"student_dir  {student_dir}")

elements = collections.defaultdict(lambda: collections.defaultdict(set))

for path in glob.glob(instructor_dir+"/chapter*/*/*.dfy"):
    postfix = path[len(instructor_dir)+1:]
    (chapter,type,filename) = postfix.split("/")
    #print((chapter,type,filename))
    elements[chapter][type].add(filename)

for chapter in sorted(elements.keys()):
    output_chapter = os.path.join(student_dir, chapter)

    # Destroy existing data
    #print(output_chapter)
    shutil.rmtree(output_chapter)
    os.mkdir(output_chapter)

    for type in sorted(elements[chapter].keys()):
        if type != "solutions":
            for filename in sorted(elements[chapter][type]):
                print(type, filename)
                try:
                    os.makedirs(os.path.join(student_dir, chapter, type))
                except FileExistsError: pass
                shutil.copyfile(
                    os.path.join(instructor_dir, chapter, type, filename),
                    os.path.join(student_dir, chapter, type, filename))
