//   SHACL RDF shape checker
//
// This is or was https://linkeddata.github.io/shacl-check
// MIT Licence
//
// This is probably incomplete implementation of SHACL
// See https://www.w3.org/TR/shacl/

const $rdf = require('rdflib')
const RDF = $rdf.Namespace('http://www.w3.org/1999/02/22-rdf-syntax-ns#')
const sh = $rdf.Namespace('http://www.w3.org/ns/shacl#')
const a = RDF('type')

// see sh:nodeKind for these values
const termTypeMap = {'NamedNode': 'IRI'}

class ShapeChecker {
  constructor (kb, shapeDoc, targetDoc, reportDoc, options) {
    this.kb = kb
    this.shapeDoc = shapeDoc
    this.targetDoc = targetDoc
    this.reportDoc = reportDoc
    this.options = options || {} // eg noResultMessage
    if (reportDoc) {
      this.report = this.kb.bnode()
      // this.report = this.kb.sym(reportDoc.uri + '#this')
      this.kb.add(this.report, a, sh('ValidationReport'), this.reportDoc)
    } else {
      console.log('ShapeChecker: NO REPORT DOCUMENT GIVEN')
    }
  }

  complain (message) {
    console.log(message)
  }

  // See https://www.w3.org/TR/shacl/#validation-report
  validationResult (issue) {
    this.conforms = false
    if (this.reportDoc) {
      let result = this.kb.bnode()
      this.kb.add(this.report, sh('result'), result, this.reportDoc)
      this.kb.add(result, a, sh('ValidationResult'), this.reportDoc)
      this.kb.add(result, sh('focusNode'), issue.node, this.reportDoc)
      this.kb.add(result, sh('sourceShape'), issue.shape, this.reportDoc)
      if (issue.path) this.kb.add(result, sh('resultPath'), issue.path, this.reportDoc)
      if (issue.object !== undefined) {
        this.kb.add(result, sh('value'), issue.object, this.reportDoc)
      }
      if (!this.options.noResultMessage) {
        this.kb.add(result, sh('resultMessage'), issue.message, this.reportDoc)
      }
      let severity = this.kb.any(issue.shape, sh('severity')) || sh('Violation')
      this.kb.add(result, sh('resultSeverity'), severity, this.reportDoc)
      this.kb.add(result, sh('sourceConstraintComponent'), sh(issue.cc + 'ConstraintComponent'), this.reportDoc)
    }
  }

  // Find any shapes which should be applied to nodes
  execute () {
    const checker = this
    const kb = this.kb
    this.conforms = true
    const post = function (issues) {
      if (!issues) return
      for (let i = 0; i < issues.length; i++) {
        checker.validationResult(issues[i])
      }
    }
    kb.statementsMatching(null, sh('targetClass'), null, this.shapeDoc)
      .forEach(function (st) {
        var targetClass = st.object
        var shape = st.subject
        console.log('Target class ' + targetClass)
        kb.each(null, a, targetClass).forEach(function (target) {
          console.log('Target class member ' + target)
          post(checker.checkNodeShape(target, shape))
        })
      })
    kb.statementsMatching(null, sh('targetNode'), null, this.shapeDoc)
      .forEach(function (st) {
        var target = st.object
        var shape = st.subject
        console.log('Target node ' + target)
        post(checker.checkNodeShape(target, shape))
      })

    if (this.reportDoc) {
      kb.add(this.report, sh('conforms'), this.conforms, this.reportDoc)
    }
  }

  // Return an array of nodes at the end of the path
  followPath (node, path) {
    const checker = this
    let pred = this.kb.any(path, sh('inversePath'))
    if (pred) {
      return this.kb.each(null, pred, node)
    }

    if (path.termType === 'Collection') { // A base list is a sequence
      var results = []
      var followSeq = function (node, array) {
        if (array.length === 0) {
          results.push(node)
        }
        checker.followPath(node, array[0]).forEach(function (next) {
          followSeq(next, array.slice(1))
        })
      }
      followSeq(node, path.elements)
      return results
    }

    let alt = this.kb.any(path, a, sh('alternative'))
    if (alt) {
      let results = []
      for (let i = 0; i < alt.length; i++) {
        results = results.concat(checker.followPath(alt.elements[i]))
      }
      return results
    }

    let sub = this.kb.any(path, a, sh('oneOrMorePath'))
    if (sub) {
      let soFar = checker.followPath(node, sub)
      if (soFar.length === 0) {
        this.complain('Sould be at least one')
      }
      return soFar
    }

    sub = this.kb.any(path, a, sh('zeroOrMorePath'))
    if (sub) {
      let soFar = checker.followPath(node, sub)
      // if (soFar.length ) // Semantics if this?
      return soFar
    }

    sub = this.kb.any(path, a, sh('zeroOrOnePath'))
    if (sub) {
      let soFar = checker.followPath(node, sub)
      if (soFar.length > 1) {
        this.complain('Sould be no more than one')
      }
      return soFar
    }

    // default is this is just a forward predicate
    return this.kb.each(node, path)
  }

  // Returns an array of issues else false
  //
  checkNodeShape (node, shape) {
    const kb = this.kb
    const checker = this
    console.log(' Applying shape ' + shape)
    console.log('        to node ' + node)

    var closed = kb.anyValue(shape, sh('closed'))
    closed = {'true': true, '1': true}[closed] || false
    console.log('  closed: ' + closed)
    var allowed = []
    if (closed) {
      var ignoredProperties = kb.any(shape, sh('ignoredProperties'))
      if (ignoredProperties) {
        ignoredProperties = ignoredProperties.elements
        for (let k = 0; k < ignoredProperties.length; k++) {
          console.log('      Ignoreable: ' + ignoredProperties[k])
          allowed[ignoredProperties[k].uri] = true
        }
      }
    }
    var issues = []
    const noteIssue = function (issue) {
      console.log('  -> ' + issue.message)
      issues.push(issue)
    }
    kb.each(shape, sh('property')).forEach(function (property) {
      let path = kb.the(property, sh('path')) // Assume simple predicate at this stage
      if (!path) {
        console.log('@@ NO PATH! ' + kb.connectedStatements(property).length)
        console.log('as subject: ' + kb.statementsMatching(property).length)
        console.log('as object: ' + kb.statementsMatching(null, null, property).length)
        console.log('property: ' + property)
        console.log('shape: ' + shape)
        console.log('about shape: ' + kb.connectedStatements(shape).map(x => x.toNT()))
        console.log('node: ' + node)
        process.exit(-99)
      }
      console.log('  Checking property ' + property + ': ' + path)
      let values = checker.followPath(node, path)
      if (path.uri) {
        allowed[path.uri] = true
      }

      let minCount = kb.anyValue(property, sh('minCount'))
      if (minCount && values.length < minCount) {
        noteIssue({node, shape, path, cc: 'MinCount', message: 'Too few (' + values.length + ') ' + path + ' on ' + node})
      }
      let maxCount = kb.anyValue(property, sh('maxCount'))
      if (maxCount && values.length > maxCount) {
        noteIssue({node, shape, path, cc: 'MaxCount', message: 'Too many (' + values.length + ') ' + path + ' on ' + node})
      }
      let constraint

      for (var i = 0; i < values.length; i++) {
        let object = values[i]

        // ///// Checking for object class membership

        let constraints = kb.each(property, sh('class'))
        if (constraints) {
          constraints.forEach(function (constraint) {
            if (constraint && !kb.holds(object, a, constraint)) {
              noteIssue({node, shape, path, cc: 'Class', message: 'Error ' + object + ' should be in class ' + constraint})
            }
          })
        }

        // ////////////////////////////// Comparing with other predicates

        constraint = kb.anyValue(property, sh('equals'))
        if (constraint) {
          let others = kb.each(node, constraint) // @@ extend to general paths??
          for (let k = 0; k < others.length; k++) {
            if (!object.sameTerm(others[k])) {
              noteIssue({node, shape, path, object, cc: 'Equals', message: 'Error ' + object + ' should be equal to ' + constraint + ' that is, ' + others[k]})
            }
          }
        }
        constraint = kb.anyValue(property, sh('disjoint'))
        if (constraint) {
          let others = kb.each(node, constraint) // @@ extend to general paths??
          for (let k = 0; k < others.length; k++) {
            if (object.sameTerm(others[k])) {
              noteIssue({node, shape, path, object, cc: 'Equals', message: 'Error ' + object + ' should be NOT equal to ' + constraint + ' that is, ' + others[k]})
            }
          }
        }
        // @@ todo:  LessThan etc etc

        // /////////////////////////// Range constraints

        constraint = kb.anyValue(property, sh('minInclusive'))
        if (constraint && !(object.value && object.value >= constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, path, object, cc: 'MinInclusive', message: 'Error ' + object + ' should more than or equal to  ' + constraint})
        }
        constraint = kb.anyValue(property, sh('minExclusive'))
        if (constraint && !(object.value && object.value > constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, path, object, cc: 'MinExclusive', message: 'Error ' + object + ' should more than ' + constraint})
        }
        constraint = kb.anyValue(property, sh('maxInclusive'))
        if (constraint && !(object.value && object.value <= constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, path, object, cc: 'MaxInclusive', message: 'Error ' + object + ' should less than or equal to  ' + constraint})
        }
        constraint = kb.anyValue(property, sh('maxExclusive'))
        if (constraint && !(object.value && object.value < constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, path, object, cc: 'MaxExclusive', message: 'Error ' + object + ' should less than or equal to  ' + constraint})
        }
        constraint = kb.anyValue(property, sh('minLength'))
        if (constraint && !(object.value && object.value.length < constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, path, object, cc: 'MinLength', message: 'Error ' + object + ' should less than or equal to  ' + constraint})
        }
        constraint = kb.anyValue(property, sh('maxLength'))
        if (constraint && !(object.value && object.value.length > constraint)) { // @@@@ use som toJS to make work for any datatype
          noteIssue({node, shape, path, object, cc: 'MexLength', message: 'Error ' + object + ' should less than or equal to  ' + constraint})
        }

        // ////////////////////////////////  Others

        constraint = kb.any(property, sh('datatype'))
        if (constraint && !(object.datatype && object.datatype.sameTerm(constraint))) {
          noteIssue({node, shape, path, object, cc: 'Datatype', message: 'Error ' + object + ' should be datatype  ' + constraint})
        }
        constraint = kb.anyValue(property, sh('languageIn'))
        if (constraint) {
          let langs = constraint.elements.map(function (x) { return x.value }).join(',')
          if (!(object.lang && langs.includes(object.lang))) {
            noteIssue({node, shape, path, object, cc: 'LanguageIn', message: 'Error ' + object + ' should be in one of languages: ' + langs})
          }
        }
        constraint = kb.anyValue(property, sh('pattern'))
        if (constraint) {
          if (!(object.value && object.value.match(constraint))) {
            noteIssue({node, shape, path, object, cc: 'Pattern', message: 'Error ' + object + ' should match pattern  ' + constraint})
          }
        }
        constraint = kb.any(property, sh('nodeKind'))
        if (constraint) {
          let actual = termTypeMap[object.termType] || object.termType
          let allowed = constraint.uri.split('#')[1] // eg 'BlankNodeOrIRI'
          if (!allowed.includes(actual)) {
            noteIssue({node, shape, path, object, cc: 'NodeKind', message: 'Error ' + object + ' should be of node kind:  ' + constraint})
          }
        }

        // //////////////////// Logical ones

        constraint = kb.any(property, sh('node'))
        if (constraint && !(checker.checkNodeShape(object, constraint))) {
          noteIssue({node, shape, path, object, cc: 'Node', message: 'Error ' + object + ' should match shape  ' + constraint})
        }
        constraint = kb.any(property, sh('not'))
        if (constraint && (checker.checkNodeShape(object, constraint))) {
          noteIssue({node, shape, path, object, cc: 'Not', message: 'Error ' + object + ' should NOT match shape  ' + constraint})
        }
        constraint = kb.any(property, sh('and'))
        if (constraint) {
          let shapes = constraint.elements
          let iss = []
          for (let i = 0; i < shapes.length; i++) {
            let res = checker.checkNodeShape(object, shapes[i])
            if (res) {
              iss = iss.concat(res)
            }
          }
          if (iss.length) {
            noteIssue({node, shape, path, object, cc: 'And',
            message: 'Error ' + object + ' does not match ALL shapes  ' + constraint})
            issues = issues.concat(iss) // @@@ Give all these details too?  it is logical
          }
        }
        constraint = kb.any(property, sh('or'))

        var ok = true
        if (constraint) {
          let shapes = constraint.elements
          let iss = []
          ok = false
          for (let i = 0; i < shapes.length; i++) {
            let res = checker.checkNodeShape(object, shapes[i])
            if (res) {
              iss = iss.concat(res)
            } else {
              ok = true
            }
          }
          if (!ok) {
            noteIssue({node, shape, path, object, cc: 'Or',
            message: 'Error ' + object + ' does not match EITHER shape  ' + constraint})
          // issues = issues.concat(iss)
          }
        }
        constraint = kb.any(property, sh('xone'))
        if (constraint) {
          let shapes = constraint.elements
          // let iss = []
          let matches = 0
          for (let i = 0; i < shapes.length; i++) {
            let res = checker.checkNodeShape(object, shapes[i])
            if (res) {
              matches += 1
            // iss = iss.concat(res)
            }
          }
          if (!ok) {
            noteIssue({node, shape, path, object, cc: 'Xone',
            message: 'Error ' + object + ' does not match EXACTLY ONE shape  ' + constraint})
            // issues = issues.concat(iss)
          }
        }
      } // next value
    }) // next property
    if (closed) {
      kb.statementsMatching(node).forEach(function (st) {
        if (!allowed[st.predicate.uri]) {
          noteIssue({shape, node, object: st.object, cc: 'Closed', message: 'Closed node has extra data: ' + st})
        }
      })
    }
    return issues.length ? issues : false
  } // method
} // End of class ShapeChecker

module.exports = ShapeChecker

// //////////////////////////////
