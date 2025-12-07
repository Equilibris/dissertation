// Todo collection system for Typst documents

#let todo-counter = counter("todo-counter")
#let todo-list = ()

#let todo(body) = context {
  // Generate unique label for this todo
  todo-counter.step()
  let todo-label = label("todo-" + str(todo-counter.get().first()))

  // Add todo with label to the global list
  todo-list.push((body, todo-label))

  // Display the todo inline with formatting
  box(
    fill: rgb("#fff3cd"),
    stroke: rgb("#856404"),
    inset: 3pt,
    radius: 2pt,
    [*TODO:* #body]
  ) + todo-label
}

#let show-todos() = {
  // Display all collected todos
  if todo-list.len() > 0 {
    heading(level: 2)[Outstanding TODOs]
    for (i, todo-item) in todo-list.enumerate() [
      #(i + 1). #todo-item.first()
    ]
  }
}
