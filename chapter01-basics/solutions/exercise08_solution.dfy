//#title Type synonyms

// So by now you see me composing types and you're itching to
// construct some of your own.

// First, type renaming:
type SeqOfSets = seq<set<int>>

lemma TryATypeSynonym()
{
  var seqOfSets:SeqOfSets := [{0}, {0,1}, {0,1,2}];
//#exercise  assert 1 in seqOfSets[0];
//#start-elide
  assert 1 in seqOfSets[1];
//#end-elide
}

