/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact.hibernate;

/**
 * A (default) Hiberante-based implementation for the interface ArchEResponsibilityStructure. 
 * A responsibility structure is a container for responsibilities along with 
 * relations between them (as specified for a particular reasoning framework)
 * <p>
 * Two core relations used by ArchE are translation and refinement relations. 
 * A translation relation maps a scenario to a* responsibility. A refinement 
 * establishes a 'specialization' of a general responsibility into a more 
 * concrete responsibility. These two types of relations cannot be customized 
 * by external reasoning framework.
 * <p>
 * Each external reasoning framework is expected to have its own responsibility
 * structure, and then manage its own types of responsibility relations 

 * @author Hyunwoo Kim, Andres Diaz-Pace
 */

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

import org.hibernate.Hibernate;
import org.hibernate.HibernateException;
import org.hibernate.Query;
import org.hibernate.Session;

import arche.modifChangeImpact.hibernate.vo.ArchERefinementRelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchERelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityStructureVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityVO;
import arche.modifChangeImpact.hibernate.vo.ArchEScenarioVO;
import arche.modifChangeImpact.hibernate.vo.ArchETranslationRelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;

import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEArchitecture;
import edu.cmu.sei.arche.external.data.ArchERelation;
import edu.cmu.sei.arche.external.data.ArchEResponsibility;
import edu.cmu.sei.arche.external.data.ArchEResponsibilityStructure;
import edu.cmu.sei.arche.external.data.ArchEScenario;

public class ArchECoreResponsibilityStructure implements ArchEResponsibilityStructure {

	protected ArchECoreArchitecture parent;
	protected ArchEVersionVO version;
	
	protected ArchEResponsibilityStructureVO rawRSVO; 

	protected List<ArchETranslationRelationVO> trVOs; // For translation relations
	protected List<ArchERefinementRelationVO> refVOs; // For refinement relations

	private List<ArchERelation> removedRelationVOs = null; // For any relation that is 'removed' from the structure	
	
	public ArchECoreResponsibilityStructure(ArchECoreArchitecture architecture) {		
		// Set parent and version info.
		this.parent = architecture;
		this.version = (ArchEVersionVO)architecture.getCurrentVersion();
		
		this.rawRSVO = new ArchEResponsibilityStructureVO();
		this.trVOs = new ArrayList<ArchETranslationRelationVO>();		
		this.refVOs = new ArrayList<ArchERefinementRelationVO>();		
		
		removedRelationVOs = new ArrayList<ArchERelation>();				
	}

	public ArchEArchitecture getParent(){
		return parent;
	}	

	/**
	 * Restore all the VOs related to this core responsibility structure
	 */
	public void restore() throws ArchEException{				
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
		    	// Restore a raw responsibility structure
		    	rawRSVO = (ArchEResponsibilityStructureVO)(openSession
		    			.createQuery("from ArchEResponsibilityStructureVO as v where v.id = ?")
						.setInteger(0, version.getId()).uniqueResult());
		    	
		    	// Lazy initialization of collections
		    	Hibernate.initialize(rawRSVO.getResponsibilities());
		    	
		    	for(Iterator<ArchEResponsibilityVO> itResps = rawRSVO.getResponsibilities().iterator(); itResps.hasNext();) 
		    		this.restoreParametersForResponsibility(itResps.next(), openSession);
		    	
		    	// Restore the translation relations from requirements to responsibilities
		    	Query qrels = ArchECoreDataProvider.getSessionFactory()
		    			.getCurrentSession().createQuery("from ArchETranslationRelationVO as rel where rel.parentType = ? and rel.version = ?");
		    	qrels.setString(0,"Scenario");
		    	qrels.setInteger(1, version.getId());
		    	trVOs = qrels.list();	    				

		    	// Restore the refinement relations (between responsibilities)
		    	Query qrefs = ArchECoreDataProvider.getSessionFactory()
		    			.getCurrentSession().createQuery("from ArchERefinementRelationVO as rel where rel.version = ?");
		    	qrefs.setInteger(0, version.getId());
		    	refVOs = qrefs.list();	    				
	    	
			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}
		}
	}
	
	/** 
	 * Save all the VOs related to this core responsibility structure
	 */
	public void save() throws ArchEException{
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
		    	// Save or update the raw responsibility structure
//				openSession.saveOrUpdate(rawRSVO);

				for(Iterator<ArchEResponsibilityVO> itResps = rawRSVO.getResponsibilities().iterator(); itResps.hasNext();) 
				{
					ArchEResponsibilityVO resp = itResps.next();
					String name = resp.getName();
					openSession.saveOrUpdate(resp);
		    		this.saveParametersForResponsibility(resp, openSession);			
				}
			
		    	// Save or update the translation relations	
				for(Iterator<ArchETranslationRelationVO> it = trVOs.iterator(); it.hasNext() ; )
					openSession.saveOrUpdate(it.next());			

		    	// Save or update the refinement relations	
				for(Iterator<ArchERefinementRelationVO> it = refVOs.iterator(); it.hasNext() ; )
					openSession.saveOrUpdate(it.next());			

				// It deletes the list of 'removed' VOs
				for (Iterator it = removedRelationVOs.iterator(); it.hasNext();)
					openSession.delete(it.next());				
				
			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}
	}
	
	/** 
	 * This is a hook method to delete any parameter whose factId doesn't
	 * correspond to any actual responsibility/relation. This method should
	 * be invoked by subclasses after saving the responsibilityStructure to the database
     * 
	 * @param openSession The current Hibernate session (for SQL queries) 
	 * @param version The version for accessing the properties
	 */
	protected void deleteDanglingParameters(Session openSession, ArchEVersionVO version) {
		return;
	}
	
	/**
	* This is a hook method that is expected to  be overridden by an  
	* ArchECoreResponsibilityStructure subclass in order to load specific properties for 
	* a responsibility
    * 
	* @param responsibility The parent responsibility to look for properties
    * @param openSession The current Hibernate session (for SQL queries) 
	*/
	protected void restoreParametersForResponsibility(ArchEResponsibilityVO responsibility, 
				Session openSession) {
		return;
	}

	/**
	* This is a hook method that is expected to  be overridden by an  
	* ArchECoreResponsibilityStructure subclass in order to save specific properties for a 
	* responsibility
    * 
	* @param responsibility The parent responsibility to look for properties
    * @param openSession The current Hibernate session (for SQL queries) 
	*/
	protected void saveParametersForResponsibility(ArchEResponsibilityVO responsibility, 
				Session openSession) {
		return;
	}

	/**
	* This is a hook method that is expected to  be overridden by an  
	* ArchECoreResponsibilityStructure subclass in order to save (save as) specific 
	* properties for a responsibility
    * 
	* @param newVersion The version for the new parameters being saved
	* @param responsibility The parent responsibility to look for properties
    * @param openSession The current Hibernate session (for SQL queries) 
	*/
	protected void saveParametersForResponsibilityAs(ArchEVersionVO newVersion, 
				ArchEResponsibilityVO responsibility, Session openSession) {
		return;
	}
	
	/**
	* This is a hook method that is expected to  be overridden by an  
	* ArchECoreResponsibilityStructure subclass in order to load specific properties for a relation
    * 
	* @param relation The parent relation to look for properties
    * @param openSession The current Hibernate session (for SQL queries) 
	*/
	protected void restoreParametersForRelation(ArchERelationVO relation, Session openSession) {
		return;
	}

	/**
	* This is a hook method that is expected to  be overridden by an  
	* ArchECoreResponsibilityStructure subclass in order to save specific properties for a relation
    * 
	* @param relation The parent relation to look for properties
    * @param openSession The current Hibernate session (for SQL queries) 
	*/
	protected void saveParametersForRelation(ArchERelationVO relation, Session openSession) {
		return;
	}

	/**
	* This is a hook method that is expected to  be overridden by an  
	* ArchECoreResponsibilityStructure subclass in order to save (save as) specific properties 
	* for a relation
    * 
	* @param newVersion The version for the new parameters being saved
	* @param relation The parent relation to look for properties
    * @param openSession The current Hibernate session (for SQL queries) 
	*/
	protected void saveParametersForRelationAs(ArchEVersionVO newVersion, ArchERelationVO relation, 
					Session openSession) {
		return;
	}	
	
	/** 
	 * Save AS all the VOs related to this core responsibility structure	   
     * 
	 * @param newVersion The version for the new VOs
	 * @throws ArchEException      
	 */
	public void saveAs(ArchEVersionVO newVersion) throws ArchEException {
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
			
				// Save the newly-created raw responsibility structure
				rawRSVO.setId(newVersion.getId());
				
				ArchEResponsibilityVO itemResp = null;
				for(Iterator<ArchEResponsibilityVO> it = rawRSVO.getResponsibilities().iterator(); it.hasNext();){
					itemResp = it.next();
					itemResp.setVersion(newVersion);
					openSession.save(itemResp);
		    		this.saveParametersForResponsibilityAs(newVersion, itemResp, openSession);
				}
				
				// Create a copy of the existing translation relations
				ArchETranslationRelationVO itemTr = null;
				for(Iterator<ArchETranslationRelationVO> it = trVOs.iterator(); it.hasNext();) {
					itemTr = it.next();
					itemTr.setVersion(newVersion);
					openSession.save(itemTr);			
				}		

				// Create a copy of the existing refinement relations
				ArchERefinementRelationVO itemRef = null;
				for(Iterator<ArchERefinementRelationVO> it = refVOs.iterator(); it.hasNext();) {
					itemRef = it.next();
					itemRef.setVersion(newVersion);
					openSession.save(itemRef);			
				}		

			} catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}
	}

	/** 
	 * Delete all the VOs related to this core responsibility structure
     * 
	 * @throws ArchEException      
	 */
	public void delete() throws ArchEException{
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
				// Delete the raw responsibility structure
				openSession.delete(rawRSVO);
				
				for(Iterator<ArchEResponsibilityVO> itResps = rawRSVO.getResponsibilities().iterator(); itResps.hasNext();) 
		    		this.deleteParametersForResponsibility(itResps.next(), openSession);

				// Delete the translation relations
				for (Iterator<ArchETranslationRelationVO> itTr = trVOs.iterator(); itTr.hasNext();)
					openSession.delete(itTr.next());

				// Delete the refinement relations
				for (Iterator<ArchERefinementRelationVO> itRef = refVOs.iterator(); itRef.hasNext();)
					openSession.delete(itRef.next());

			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}
	}
	
	/**
	* This is a hook method that is expected to  be overridden by an  
	* ArchECoreResponsibilityStructure subclass in order to delete specific properties 
	* for a responsibility
    * 
	* @param responsibility The parent responsibility to look for properties
    * @param openSession The current Hibernate session (for SQL queries) 
	*/
	protected void deleteParametersForResponsibility(ArchEResponsibilityVO responsibility, 
			Session openSession) {
		return;
	}

	/**
	* This is a hook method that is expected to  be overridden by an  
	* ArchECoreResponsibilityStructure subclass in order to delete specific properties 
	* for a relationship
    * 
	* @param relation The parent relation to look for properties
    * @param openSession The current Hibernate session (for SQL queries) 
	*/
	protected void deleteParametersForRelation(ArchERelationVO relation, Session openSession) {
		return;
	}
	
	public List<ArchEResponsibility> getResponsibilities() {
		List<ArchEResponsibility> responsibilityList = new ArrayList(rawRSVO.getResponsibilities());
    	return responsibilityList;
	}
	

	/** 
	 * Return those responsibilities that are linked to a particular scenario (via translation relations)
	 * 
     * @param scenario The parent scenario
	 */
	public List<ArchEResponsibility> getResponsibilitiesByScenario(
			ArchEScenario scenario) {
		List<ArchEResponsibility> responsibilitiesOfInterest = new ArrayList<ArchEResponsibility>();
		
		ArchETranslationRelationVO item = null;
		for(Iterator<ArchETranslationRelationVO> it = trVOs.iterator(); it.hasNext();){
			item = it.next();
			// TODO: Check if an equal 'by name' works better here
			ArchEScenarioVO parent = item.getParent();
			ArchEResponsibility child = item.getChild();
			if ( (parent != null)
					&& parent.equals((ArchEScenarioVO)scenario)
					&& child != null)  
				responsibilitiesOfInterest.add(child);
		}		
    	return (responsibilitiesOfInterest);
	}

	/** 
	 * Return the refinements (children responsibilities) of a given responsibility
	 * 
     * @param parentResponsibility The parent responsibility
	 */
	public List<ArchEResponsibility> getChildrenResponsibilities(
			ArchEResponsibility parentResponsibility) {
		List<ArchEResponsibility> children = new ArrayList<ArchEResponsibility>();
		
		ArchERefinementRelationVO item = null;
		for(Iterator<ArchERefinementRelationVO> it = refVOs.iterator(); it.hasNext();){
			item = it.next();
			// TODO: Check if an equal 'by name' works better here
			ArchEResponsibility parent = item.getParent();
			if ( (parent != null) 
					&& parent.equals(parentResponsibility)
					&& item.getChild() != null)  
				children.add(item.getChild());
		}		
    	return (children);
	}

	/** 
	 * Return all the responsibilities a given responsibility is child of (due to
	 * refinement relations) 
	 * 
     * @param childResponsibility The child responsibility
	 */
	public List<ArchEResponsibility> getParentResponsibilities(
			ArchEResponsibility childResponsibility) {
		List<ArchEResponsibility> parents = new ArrayList<ArchEResponsibility>();
		
		ArchERefinementRelationVO item = null;
		for(Iterator<ArchERefinementRelationVO> it = refVOs.iterator(); it.hasNext();){
			item = it.next();
			// TODO: Check if an equal 'by name' works better here
			if ( (item.getChild() != null) && 
					(item.getChild().equals(childResponsibility) && item.getParent() != null))  
				parents.add(item.getParent());
		}
		
    	return (parents);
	}

	/** 
	 * Test if a given responsibility has been refined 
	 * 
     * @param responsibility The parent responsibility
	 */
	public boolean isLeaf(ArchEResponsibility responsibility) {
		ArchERefinementRelationVO item = null;
		for(Iterator<ArchERefinementRelationVO> it = refVOs.iterator(); it.hasNext();){
			item = it.next();
			// TODO: Check if an equal 'by name' works better here
			ArchEResponsibility parent = item.getParent();
			if ( (parent != null)
					&& parent.equals(responsibility)
					&& item.getChild()!= null)  
				return (false);
		}
		
		return (true);
	}

	public boolean addResponsibility(ArchEResponsibility resp) {	
		return rawRSVO.getResponsibilities().add((ArchEResponsibilityVO)resp);
	}

	/** 
	 * Hook method for adding reasoning-framework-specific relations to the responsibility
	 * structure 
	 * 
     * @param relation The relation being added
	 */
	public boolean addRelation(ArchERelation relation) {
		// Note: We do allow addition of translation relations (by tactics)
		if (relation instanceof ArchETranslationRelationVO) {
			return (trVOs.add((ArchETranslationRelationVO)relation));
		}
		return (false);
	}

	/** 
	 * Stores a reasoning-framework-specific relation for further deletion
	 * when invoking the save() operation (Hibernate-related issue). Afterwards,
	 * the target relation shouldn't be used by the reasoning framework anymore.
	 * 
     * @param relation The target relation
	 */
	public boolean deleteRelation(ArchERelation relation) {
		removedRelationVOs.add(relation);
		// Note: We do allow deletion of translation relations (by tactics)
		if (relation instanceof ArchETranslationRelationVO)
			return (trVOs.remove(relation));
		if (relation instanceof ArchERefinementRelationVO)
			return (refVOs.remove(relation));
		return (false);
	}

	/** 
	 * Test whether there is a relation of a given type between two responsibilities
	 * 
     * @param resp1 The source responsibility
     * @param resp2 The target responsibility
     * @param relationTypeVO The relation type (VO class name)
	 */
	public boolean existRelation(ArchEResponsibility resp1, ArchEResponsibility resp2, String relationTypeVO) {
		return (this.getRelation(resp1, resp2, relationTypeVO) != null);
	}

	/** 
	 * Test whether there is a relation of a given type between two responsibilities. In
	 * case the relation exists, it is returned by the method
	 * 
     * @param resp1 The source responsibility
     * @param resp2 The target responsibility
     * @param relationTypeVO The relation type (VO class name)
	 */
	public ArchERelation getRelation(ArchEResponsibility resp1, ArchEResponsibility resp2, String relationTypeVO) {
		List<ArchERelation> list = this.getRelations(relationTypeVO);
		ArchERelation rel = null;
		for (Iterator<ArchERelation> it = list.iterator(); it.hasNext();) {
			rel = it.next(); // TODO: Check if an equal 'by name' is needed below
			ArchEResponsibility parent = (ArchEResponsibility)rel.getParent();
			ArchEResponsibility child = (ArchEResponsibility)rel.getChild();
			if ((parent != null)
					&& (child != null)
					&& parent.equals(resp1)
					&& child.equals(resp2))
				return (rel);
			if ((parent != null)
					&& (child != null)
					&& parent.equals(resp2) 
					&& child.equals(resp1))
				return (rel);
		}
		return (null);
	}
	
	public ArchERelation getRelation(ArchEScenario sc, ArchEResponsibility resp) {
		List<ArchERelation> list = this.getRelations(ArchETranslationRelationVO.class.getName());
		ArchERelation rel = null;
		for (Iterator<ArchERelation> it = list.iterator(); it.hasNext();) {
			rel = it.next(); // TODO: Check if an equal 'by name' is needed below
			ArchEScenario parent = (ArchEScenario)rel.getParent();
			ArchEResponsibility child = (ArchEResponsibility)rel.getChild();
			if ((parent != null)
					&& (child != null)
					&& parent.equals(sc) 
					&& child.equals(resp))
				return (rel);
		}
		return (null);
	}

	public boolean containResponsibility(ArchEResponsibility responsibility) {
		for (Iterator<ArchEResponsibilityVO> it = rawRSVO.getResponsibilities().iterator(); it.hasNext();) {
			// Two responsibilities are equal if they have the same name
			// (under the same version of the architecture)
			if (it.next().getName().equals(responsibility.getName()))
				return (true);
		}
		return (false);
	}
	
	/** 
	 * Return all the reasoning-framework-specific relations of a given type that
	 * have been defined within the responsibility structure
	 * 
     * @param relationTypeVO The relation type (VO class name)
	 */
	public List<ArchERelation> getRelations(String relationTypeVO) {
		// TODO: Review the type conversions below
		ArchERelation[] result = null;
		if (relationTypeVO.equals(ArchETranslationRelationVO.class.getName())) {
			result = new ArchERelation[trVOs.size()];
			result = trVOs.toArray(result);
			return (Arrays.asList(result));
		}
		else if (relationTypeVO.equals(ArchERefinementRelationVO.class.getName())) {
			result = new ArchERelation[refVOs.size()];
			result = refVOs.toArray(result);
			return (Arrays.asList(result));
		}
		else
			return (null);
		
	}

	/** 
	 * Establish a refinement relation between two existing responsibilities
	 * 
     * @param parent The source responsibility
     * @param child The target responsibility
	 */
	public boolean refineResponsibility(ArchEResponsibilityVO parent, ArchEResponsibilityVO child) {
		
		ArchERelation rel = this.getRelation(parent, child, ArchERefinementRelationVO.class.getName());
		
		if (rel == null) { // There's no previous refinement between the two responsibilities
			
			ArchERefinementRelationVO refinement = new ArchERefinementRelationVO(this.version);
			refinement.setParent(parent);
			refinement.setChild(child);
			refVOs.add(refinement);
			
			// The child in the refinement relation "inherits" the scenario 
			// translations from its parent responsibility
			ArchETranslationRelationVO translation = null;
			ArchETranslationRelationVO newTranslation = null;
			ArchEScenarioVO baseScenario = null;
			List<ArchETranslationRelationVO> derivedTranslations = new ArrayList<ArchETranslationRelationVO>();
			for (Iterator<ArchETranslationRelationVO> it = trVOs.iterator(); it.hasNext();) {
				translation = it.next();
				
				baseScenario = translation.getParent();
				if (parent.equals(translation.getChild()) && !this.existTranslation(baseScenario, child)) { 
					// A translation relation exists for the parent responsibility
					newTranslation = new ArchETranslationRelationVO(this.version);
					newTranslation.setParent(baseScenario);
					newTranslation.setChild(child);					
					derivedTranslations.add(newTranslation);
				}
			}

			for (Iterator<ArchETranslationRelationVO> it = derivedTranslations.iterator(); it.hasNext();) 
				trVOs.add(it.next());

			return (true);
		}
		
		return (false);
	}
	
	/** 
	 * Test whether there is a translation relationship between a scenario and a responsibility
	 * 
     * @param scenario The source scenario
     * @param resp The target responsibility
	 */
	public boolean existTranslation(ArchEScenarioVO scenario, ArchEResponsibilityVO resp) {
		ArchETranslationRelationVO rel = null;
		for (Iterator<ArchETranslationRelationVO> it = trVOs.iterator(); it.hasNext();) {
			rel = it.next(); // TODO: Check if an equal 'by name' is needed below
			ArchEScenarioVO parent = rel.getParent();
			ArchEResponsibilityVO child = rel.getChild();
			if ((parent != null)
					&& (child != null)
					&& parent.equals(scenario) 
					&& child.equals(resp))
				return (true);
		}
		return (false);		
	}

	/** 
	 * Test whether there is a refinement relationship between a pair of responsibilities
	 * 
     * @param resp The source responsibility
     * @param leaf The target responsibility
	 */
	public boolean existRefinement(ArchEResponsibilityVO resp, ArchEResponsibilityVO leaf) {
		ArchERefinementRelationVO rel = null;
		for (Iterator<ArchERefinementRelationVO> it = refVOs.iterator(); it.hasNext();) {
			rel = it.next(); // TODO: Check if an equal 'by name' is needed below
			ArchEResponsibilityVO parent = rel.getParent();
			ArchEResponsibilityVO child = rel.getChild();
			if ((parent != null)
					&& (child != null)
					&& parent.equals(resp) 
					&& child.equals(leaf))
				return (true);
		}
		return (false);		
	}

}
