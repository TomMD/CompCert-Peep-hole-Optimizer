/* The Computer Language Benchmarks Game
   http://shootout.alioth.debian.org/

   Contributed by Josh Goldfoot
   to compile, use gcc -O3

   This revision uses "simple_hash.h," available from
   http://alioth.debian.org/plugins/scmcvs/cvsweb.php/shootout/bench/Include/?cvsroot=shootout
N = 1 million
*/
#include <stdio.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include "simple_hash.h"

long
hash_table_size (int fl, long buflen)
{
  long maxsize1, maxsize2;

  maxsize1 = buflen - fl;
  maxsize2 = 4;
  while (--fl > 0 && maxsize2 < maxsize1)
    maxsize2 = maxsize2 * 4;
  if (maxsize1 < maxsize2)
    return maxsize1;
  return maxsize2;
}

struct ht_ht *
generate_frequencies (int fl, char *buffer, long buflen)
{
  struct ht_ht *ht;
  char *reader;
  long i;
  char nulled;

  if (fl > buflen)
    return NULL;

  ht = ht_create (hash_table_size (fl, buflen));
  for (i = 0; i < buflen - fl + 1; i++)
    {
      reader = &(buffer[i]);
      nulled = reader[fl];
      reader[fl] = 0x00;
      ht_find_new (ht, reader)->val++;
      reader[fl] = nulled;
    }
  return ht;
}

typedef struct ssorter
{
  char *string;
  int num;
} sorter;

void
write_frequencies (int fl, char *buffer, long buflen)
{
  struct ht_ht *ht;
  long total, i, j, size;
  struct ht_node *nd;
  sorter *s;
  sorter tmp;

  ht = generate_frequencies (fl, buffer, buflen);
  total = 0;
  size = 0;
  for (nd = ht_first (ht); nd != NULL; nd = ht_next (ht))
    {
      total = total + nd->val;
      size++;
    }
  s = calloc (size, sizeof (sorter));
  i = 0;
  for (nd = ht_first (ht); nd != NULL; nd = ht_next (ht))
    {
      s[i].string = nd->key;
      s[i++].num = nd->val;
    }
  for (i = 0; i < size - 1; i++)
    for (j = i + 1; j < size; j++)
      if (s[i].num < s[j].num)
	{
	  memcpy (&tmp, &(s[i]), sizeof (sorter));
	  memcpy (&(s[i]), &(s[j]), sizeof (sorter));
	  memcpy (&(s[j]), &tmp, sizeof (sorter));
	}
  for (i = 0; i < size; i++)
    printf ("%s %.3f\n", s[i].string, 100 * (float) s[i].num / total);
  printf ("\n");
  ht_destroy (ht);
  free (s);
}

void
write_count (char *searchFor, char *buffer, long buflen)
{
  struct ht_ht *ht;

  ht = generate_frequencies (strlen (searchFor), buffer, buflen);
  printf ("%d\t%s\n", ht_find_new (ht, searchFor)->val, searchFor);
  ht_destroy (ht);
}

int
main ()
{
  char c;
  char *line, *buffer, *tmp, *x;
  int i, linelen, nothree;
  long buflen, seqlen;

  line = malloc (256);
  if (!line)
    return -1;
  seqlen = 0;
  nothree = 1;

  while (nothree && fgets (line, 255, stdin))
    if (line[0] == '>' && line[1] == 'T' && line[2] == 'H')
      nothree = 0;
  free (line);

  buflen = 10240;
  buffer = malloc (buflen + 1);
  if (!buffer)
    return -1;
  x = buffer;

  while (fgets (x, 255, stdin))
    {
      linelen = strlen (x);
      if (linelen)
	{
	  if (x[linelen - 1] == '\n')
	    linelen--;
	  c = x[0];
	  if (c == '>')
	    break;
	  else if (c != ';')
	    {
	      seqlen = seqlen + linelen;
	      if (seqlen + 512 >= buflen)
		{
		  buflen = buflen + 10240;
		  tmp = realloc (buffer, buflen + 1);
		  if (tmp == NULL)
		    return -1;
		  buffer = tmp;
		  x = &(buffer[seqlen]);
		}
	      else
		x = &(x[linelen]);
	      x[0] = 0;
	    }
	}
    }
  for (i = 0; i < seqlen; i++)
    buffer[i] = toupper (buffer[i]);
  write_frequencies (1, buffer, seqlen);
  write_frequencies (2, buffer, seqlen);
  write_count ("GGT", buffer, seqlen);
  write_count ("GGTA", buffer, seqlen);
  write_count ("GGTATT", buffer, seqlen);
  write_count ("GGTATTTTAATT", buffer, seqlen);
  write_count ("GGTATTTTAATTTATAGT", buffer, seqlen);
  free (buffer);
  return 0;
}
