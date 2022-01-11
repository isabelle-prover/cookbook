# Common Errors

<ol>
{% for item in site.data.common_errors %}
<li>
<details>
  <summary>
  <code>{{ item.error_msg }}</code>
  </summary>

  {{ item.explanation | markdownify }}

</details>
</li>
{% endfor %}
</ol>

<!-- Bad name: "a :: bool" -->
