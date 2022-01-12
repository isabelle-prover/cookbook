# Common Pitfalls

<ol>
{% for item in site.data.common_pitfalls %}
<li>
<details>
  <summary>{{ item.title }}</summary>

  {{ item.explanation }}

</details>
</li>
{% endfor %}
</ol>

