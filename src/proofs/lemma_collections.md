# Lemma Collections

The default setup of the simplifier and other automatic proof methods in Isabelle includes lemmas which are considered generally useful
and (almost) never make a goal harder to prove (or unprovable).
Apart from this default setup, Isabelle offers some collections of lemmas that are useful to prove specific kinds of goals:

<table>
<tr>
  <th>Collection</th>
  <th>Usage</th>
</tr>
{% for item in site.data.lemma_collections %}
<tr>
  <td><code>{{ item.name }}</code></td>
  <td>{{ item.explanation }}</td>
</tr>
{% endfor %}
</table>
