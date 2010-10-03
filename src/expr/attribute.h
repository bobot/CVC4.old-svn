/*********************                                                        */
/*! \file attribute.h
 ** \verbatim
 ** Original author: mdeters
 ** Major contributors: dejan
 ** Minor contributors (to current version): cconway, taking
 ** This file is part of the CVC4 prototype.
 ** Copyright (c) 2009, 2010  The Analysis of Computer Systems Group (ACSys)
 ** Courant Institute of Mathematical Sciences
 ** New York University
 ** See the file COPYING in the top-level source directory for licensing
 ** information.\endverbatim
 **
 ** \brief Node attributes.
 **
 ** Node attributes.
 **/

#include "cvc4_private.h"

/* There are strong constraints on ordering of declarations of
 * attributes and nodes due to template use */
#include "expr/node.h"
#include "expr/type_node.h"

#ifndef __CVC4__EXPR__ATTRIBUTE_H
#define __CVC4__EXPR__ATTRIBUTE_H

#include <stdint.h>

#include <string>
#include <ext/hash_map>

#include "context/cdmap.h"
#include "expr/node.h"
#include "util/output.h"

// include supporting templates
#define CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H
#include "expr/attribute_internals.h"
#undef CVC4_ATTRIBUTE_H__INCLUDING__ATTRIBUTE_INTERNALS_H

namespace CVC4 {
namespace expr {
namespace attr {

// ATTRIBUTE MANAGER ===========================================================

/**
 * A container for the main attribute tables of the system.  There's a
 * one-to-one NodeManager : AttributeManager correspondence.
 */
class AttributeManager {

  // IF YOU ADD ANY TABLES, don't forget to add them also to the
  // implementation of deleteAllAttributes().

  /** Underlying hash table for boolean-valued attributes */
  AttrHash<bool> d_bools;
  /** Underlying hash table for integral-valued attributes */
  AttrHash<uint64_t> d_ints;
  /** Underlying hash table for node-valued attributes */
  AttrHash<TNode> d_tnodes;
  /** Underlying hash table for node-valued attributes */
  AttrHash<Node> d_nodes;
  /** Underlying hash table for types attributes */
  AttrHash<TypeNode> d_types;
  /** Underlying hash table for string-valued attributes */
  AttrHash<std::string> d_strings;
  /** Underlying hash table for pointer-valued attributes */
  AttrHash<void*> d_ptrs;

  // IF YOU ADD ANY TABLES, don't forget to add them also to the
  // implementation of deleteAllAttributes().

  /** Underlying hash table for context-dependent boolean-valued attributes */
  CDAttrHash<bool> d_cdbools;
  /** Underlying hash table for context-dependent integral-valued attributes */
  CDAttrHash<uint64_t> d_cdints;
  /** Underlying hash table for context-dependent node-valued attributes */
  CDAttrHash<TNode> d_cdtnodes;
  /** Underlying hash table for context-dependent node-valued attributes */
  CDAttrHash<Node> d_cdnodes;
  /** Underlying hash table for context-dependent string-valued attributes */
  CDAttrHash<std::string> d_cdstrings;
  /** Underlying hash table for context-dependent pointer-valued attributes */
  CDAttrHash<void*> d_cdptrs;

  template <class T>
  void deleteFromTable(AttrHash<T>& table, NodeValue* nv);

  template <class T>
  void deleteFromTable(CDAttrHash<T>& table, NodeValue* nv);

  template <class T>
  void deleteAllFromTable(AttrHash<T>& table);

  /**
   * getTable<> is a helper template that gets the right table from an
   * AttributeManager given its type.
   */
  template <class T, bool context_dep>
  friend struct getTable;

public:

  /** Construct an attribute manager. */
  AttributeManager(context::Context* ctxt) :
    d_cdbools(ctxt),
    d_cdints(ctxt),
    d_cdtnodes(ctxt),
    d_cdnodes(ctxt),
    d_cdstrings(ctxt),
    d_cdptrs(ctxt) {
  }

  /**
   * Get a particular attribute on a particular node.
   *
   * @param nv the node about which to inquire
   *
   * @param const AttrKind& the attribute kind to get
   *
   * @return the attribute value, if set, or a default-constructed
   * AttrKind::value_type if not.
   */
  template <class AttrKind>
  typename AttrKind::value_type getAttribute(NodeValue* nv,
                                             const AttrKind&) const;

  /**
   * Determine if a particular attribute exists for a particular node.
   *
   * @param nv the node about which to inquire
   *
   * @param const AttrKind& the attribute kind to inquire about
   *
   * @return true if the given node has the given attribute
   */
  template <class AttrKind>
  bool hasAttribute(NodeValue* nv,
                    const AttrKind&) const;

  /**
   * Determine if a particular attribute exists for a particular node,
   * and get it if it does.
   *
   * @param nv the node about which to inquire
   *
   * @param const AttrKind& the attribute kind to inquire about
   *
   * @param ret a pointer to a return value, set in case the node has
   * the attribute
   *
   * @return true if the given node has the given attribute
   */
  template <class AttrKind>
  bool getAttribute(NodeValue* nv,
                    const AttrKind&,
                    typename AttrKind::value_type& ret) const;

  /**
   * Set a particular attribute on a particular node.
   *
   * @param nv the node for which to set the attribute
   *
   * @param const AttrKind& the attribute kind to set
   *
   * @param ret a pointer to a return value, set in case the node has
   * the attribute
   *
   * @return true if the given node has the given attribute
   */
  template <class AttrKind>
  void setAttribute(NodeValue* nv,
                    const AttrKind&,
                    const typename AttrKind::value_type& value);

  /**
   * Remove all attributes associated to the given node.
   *
   * @param nv the node from which to delete attributes
   */
  void deleteAllAttributes(NodeValue* nv);

  /**
   * Remove all attributes from the tables.
   */
  void deleteAllAttributes();
};

}/* CVC4::expr::attr namespace */

// MAPPING OF ATTRIBUTE KINDS TO TABLES IN THE ATTRIBUTE MANAGER ===============

namespace attr {

/**
 * The getTable<> template provides (static) access to the
 * AttributeManager field holding the table.
 */
template <class T, bool context_dep>
struct getTable;

/** Access the "d_bools" member of AttributeManager. */
template <>
struct getTable<bool, false> {
  typedef AttrHash<bool> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_bools;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_bools;
  }
};

/** Access the "d_ints" member of AttributeManager. */
template <>
struct getTable<uint64_t, false> {
  typedef AttrHash<uint64_t> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_ints;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_ints;
  }
};

/** Access the "d_tnodes" member of AttributeManager. */
template <>
struct getTable<TNode, false> {
  typedef AttrHash<TNode> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_tnodes;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_tnodes;
  }
};

/** Access the "d_nodes" member of AttributeManager. */
template <>
struct getTable<Node, false> {
  typedef AttrHash<Node> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_nodes;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_nodes;
  }
};

/** Access the "d_types" member of AttributeManager. */
template <>
struct getTable<TypeNode, false> {
  typedef AttrHash<TypeNode> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_types;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_types;
  }
};

/** Access the "d_strings" member of AttributeManager. */
template <>
struct getTable<std::string, false> {
  typedef AttrHash<std::string> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_strings;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_strings;
  }
};

/** Access the "d_ptrs" member of AttributeManager. */
template <class T>
struct getTable<T*, false> {
  typedef AttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_ptrs;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_ptrs;
  }
};

/** Access the "d_ptrs" member of AttributeManager. */
template <class T>
struct getTable<const T*, false> {
  typedef AttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_ptrs;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_ptrs;
  }
};

/** Access the "d_cdbools" member of AttributeManager. */
template <>
struct getTable<bool, true> {
  typedef CDAttrHash<bool> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_cdbools;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_cdbools;
  }
};

/** Access the "d_cdints" member of AttributeManager. */
template <>
struct getTable<uint64_t, true> {
  typedef CDAttrHash<uint64_t> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_cdints;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_cdints;
  }
};

/** Access the "d_tnodes" member of AttributeManager. */
template <>
struct getTable<TNode, true> {
  typedef CDAttrHash<TNode> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_cdtnodes;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_cdtnodes;
  }
};

/** Access the "d_cdnodes" member of AttributeManager. */
template <>
struct getTable<Node, true> {
  typedef CDAttrHash<Node> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_cdnodes;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_cdnodes;
  }
};

/** Access the "d_cdstrings" member of AttributeManager. */
template <>
struct getTable<std::string, true> {
  typedef CDAttrHash<std::string> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_cdstrings;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_cdstrings;
  }
};

/** Access the "d_cdptrs" member of AttributeManager. */
template <class T>
struct getTable<T*, true> {
  typedef CDAttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_cdptrs;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_cdptrs;
  }
};

/** Access the "d_cdptrs" member of AttributeManager. */
template <class T>
struct getTable<const T*, true> {
  typedef CDAttrHash<void*> table_type;
  static inline table_type& get(AttributeManager& am) {
    return am.d_cdptrs;
  }
  static inline const table_type& get(const AttributeManager& am) {
    return am.d_cdptrs;
  }
};

}/* CVC4::expr::attr namespace */

// ATTRIBUTE MANAGER IMPLEMENTATIONS ===========================================

namespace attr {

// implementation for AttributeManager::getAttribute()
template <class AttrKind>
typename AttrKind::value_type
AttributeManager::getAttribute(NodeValue* nv, const AttrKind&) const {
  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type, AttrKind::context_dependent>::
            table_type table_type;

  const table_type& ah =
    getTable<value_type, AttrKind::context_dependent>::get(*this);
  typename table_type::const_iterator i =
    ah.find(std::make_pair(AttrKind::getId(), nv));

  if(i == ah.end()) {
    return typename AttrKind::value_type();
  }

  return mapping::convertBack((*i).second);
}

/* Helper template class for hasAttribute(), specialized based on
 * whether AttrKind has a "default value" that all Nodes implicitly
 * have or not. */
template <bool has_default, class AttrKind>
struct HasAttribute;

/**
 * Specialization of HasAttribute<> helper template for AttrKinds
 * with a default value.
 */
template <class AttrKind>
struct HasAttribute<true, AttrKind> {
  /** This implementation is simple; it's always true. */
  static inline bool hasAttribute(const AttributeManager* am,
                                  NodeValue* nv) {
    return true;
  }

  /**
   * This implementation returns the AttrKind's default value if the
   * Node doesn't have the given attribute.
   */
  static inline bool getAttribute(const AttributeManager* am,
                                  NodeValue* nv,
                                  typename AttrKind::value_type& ret) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type,
                              AttrKind::context_dependent>::table_type
      table_type;

    const table_type& ah =
      getTable<value_type, AttrKind::context_dependent>::get(*am);
    typename table_type::const_iterator i =
      ah.find(std::make_pair(AttrKind::getId(), nv));

    if(i == ah.end()) {
      ret = AttrKind::default_value;
    } else {
      ret = mapping::convertBack((*i).second);
    }

    return true;
  }
};

/**
 * Specialization of HasAttribute<> helper template for AttrKinds
 * without a default value.
 */
template <class AttrKind>
struct HasAttribute<false, AttrKind> {
  static inline bool hasAttribute(const AttributeManager* am,
                                  NodeValue* nv) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type, AttrKind::context_dependent>::
              table_type table_type;

    const table_type& ah =
      getTable<value_type, AttrKind::context_dependent>::get(*am);
    typename table_type::const_iterator i =
      ah.find(std::make_pair(AttrKind::getId(), nv));

    if(i == ah.end()) {
      return false;
    }

    return true;
  }

  static inline bool getAttribute(const AttributeManager* am,
                                  NodeValue* nv,
                                  typename AttrKind::value_type& ret) {
    typedef typename AttrKind::value_type value_type;
    typedef KindValueToTableValueMapping<value_type> mapping;
    typedef typename getTable<value_type, AttrKind::context_dependent>::
              table_type table_type;

    const table_type& ah =
      getTable<value_type, AttrKind::context_dependent>::get(*am);
    typename table_type::const_iterator i =
      ah.find(std::make_pair(AttrKind::getId(), nv));

    if(i == ah.end()) {
      return false;
    }

    ret = mapping::convertBack((*i).second);

    return true;
  }
};

template <class AttrKind>
bool AttributeManager::hasAttribute(NodeValue* nv,
                                    const AttrKind&) const {
  return HasAttribute<AttrKind::has_default_value, AttrKind>::
           hasAttribute(this, nv);
}

template <class AttrKind>
bool AttributeManager::getAttribute(NodeValue* nv,
                                    const AttrKind&,
                                    typename AttrKind::value_type& ret) const {
  return HasAttribute<AttrKind::has_default_value, AttrKind>::
           getAttribute(this, nv, ret);
}

template <class AttrKind>
inline void
AttributeManager::setAttribute(NodeValue* nv,
                               const AttrKind&,
                               const typename AttrKind::value_type& value) {
  typedef typename AttrKind::value_type value_type;
  typedef KindValueToTableValueMapping<value_type> mapping;
  typedef typename getTable<value_type, AttrKind::context_dependent>::
            table_type table_type;

  table_type& ah =
    getTable<value_type, AttrKind::context_dependent>::get(*this);
  ah[std::make_pair(AttrKind::getId(), nv)] = mapping::convert(value);
}

/**
 * Search for the NodeValue in all attribute tables and remove it,
 * calling the cleanup function if one is defined.
 */
template <class T>
inline void AttributeManager::deleteFromTable(AttrHash<T>& table,
                                              NodeValue* nv) {
  for(uint64_t id = 0; id < attr::LastAttributeId<T, false>::s_id; ++id) {
    typedef AttributeTraits<T, false> traits_t;
    typedef AttrHash<T> hash_t;
    std::pair<uint64_t, NodeValue*> pr = std::make_pair(id, nv);
    if(traits_t::cleanup[id] != NULL) {
      typename hash_t::iterator i = table.find(pr);
      if(i != table.end()) {
        traits_t::cleanup[id]((*i).second);
        table.erase(pr);
      }
    } else {
      table.erase(pr);
    }
  }
}

/**
 * Obliterate a NodeValue from a (context-dependent) attribute table.
 */
template <class T>
inline void AttributeManager::deleteFromTable(CDAttrHash<T>& table,
                                              NodeValue* nv) {
  for(unsigned id = 0; id < attr::LastAttributeId<T, true>::s_id; ++id) {
    table.obliterate(std::make_pair(id, nv));
  }
}

/**
 * Remove all attributes from the table calling the cleanup function if one is defined.
 */
template <class T>
inline void AttributeManager::deleteAllFromTable(AttrHash<T>& table) {
  bool anyRequireClearing = false;
  typedef AttributeTraits<T, false> traits_t;
  typedef AttrHash<T> hash_t;
  for(uint64_t id = 0; id < attr::LastAttributeId<T, false>::s_id; ++id) {
    if(traits_t::cleanup[id] != NULL) {
      anyRequireClearing = true;
    }
  }

  if(anyRequireClearing){
    typename hash_t::iterator it = table.begin();
    typename hash_t::iterator it_end = table.end();

    while (it != it_end){
      uint64_t id = (*it).first.first;
      Debug("attrgc") << "id " << id
                      << " node_value: " << ((*it).first.second)
                      << std::endl;
      if(traits_t::cleanup[id] != NULL) {
        traits_t::cleanup[id]((*it).second);
      }
      ++it;
    }
  }
  table.clear();
}


}/* CVC4::expr::attr namespace */
}/* CVC4::expr namespace */
}/* CVC4 namespace */

#endif /* __CVC4__EXPR__ATTRIBUTE_H */
