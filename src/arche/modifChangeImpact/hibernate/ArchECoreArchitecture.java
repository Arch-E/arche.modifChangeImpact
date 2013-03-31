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
 * A (default) Hibernate-based implementation of ArchEArchitecture, as the architecture for 
 * external reasoning frameworks to work with. An architecture is seen by 
 * ArchE as a design alternative for a set of scenarios.
 * <p>
 * The architecture includes two components: a responsibility structure 
 * (for responsibilities and their relations) and a design view (for design elements 
 * and design relations). Default implementations for these two components are
 * ArchECoreResponsibilityStructure and ArchECoreView respectively.  
 * <p>
 * The architecture is a top-level container that is responsible for restoring, 
 * saving or updating its contents to the database.
 * 
 * @author Hyunwoo Kim
 */

import org.hibernate.HibernateException;
import org.hibernate.Session;

import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;

import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEArchitecture;
import edu.cmu.sei.arche.external.data.ArchEResponsibilityStructure;
import edu.cmu.sei.arche.external.data.ArchEVersion;
import edu.cmu.sei.arche.external.data.ArchEView;

public class ArchECoreArchitecture implements ArchEArchitecture {
	
	protected ArchEVersionVO versionVO; // Version for this architecture
	
	protected ArchECoreResponsibilityStructure responsibilityStructure;
	protected ArchECoreView view;
	
	public ArchECoreArchitecture(ArchEVersion version) {
		versionVO = (ArchEVersionVO)version;
		responsibilityStructure = null;
		view = null;
		//System.out.println("--> Current architecture version: "+versionVO.getId());		
	}
	
	public ArchEVersion getCurrentVersion() {
		return (ArchEVersion)versionVO;
	}	

	public ArchEResponsibilityStructure getResponsibilityStructure() {
		return (ArchEResponsibilityStructure)responsibilityStructure;
	}

	public void setResponsibilityStructure(ArchECoreResponsibilityStructure responsibilityStrcuture) {
		this.responsibilityStructure = responsibilityStrcuture;
	}
	
	public ArchEView getView() {
		return (ArchEView)view;
	}

	public void setView(ArchECoreView view) {
		this.view = view;
	}

	/**
	 * Restore this architecture from DB
	 * 
	 * @throws ArchEException
	 */
	public void restore() throws ArchEException {
		if(responsibilityStructure != null){
			// Restore the responsibility structure
			responsibilityStructure.restore();						
		}
		
		if(view != null){
			// Restore the view		
			view.restore();
		}
		
		// Restore its corresponding view (design structure) and associate each other
		// We have two options to implement this part.
		//  1) A custom data provider overwrites this method to implement this part
		// 	   if it has a view specific to its accompanying reasoning framework.
		//  2) If we have generic views sharable and interpretable by many reasoning
		//     frameworks, the views need restoring here.	
		//
		// [Example code]
		// 		MyView myView = new MyView(this);
		// 		view.restore();
		// 		this.setView(myView);
		
	}
	
	/**Persist this architecture in DB
	 * 
	 * @throws ArchEException
	 */
	public void save() throws ArchEException {
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
				
				// To update maxFactID which is used to generate a unique fact ID
				openSession.saveOrUpdate(versionVO);				
			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}						
		
		if(responsibilityStructure != null){
			// Restore the responsibility structure
			responsibilityStructure.save();						
		}
		
		if(view != null){
			// Restore the view		
			view.save();
		}
	}	

	/**Persist this architecture with a new version in DB
	 * 
	 * @param newVersion The version for the new architecture to be stored 
	 * @throws ArchEException
	 */
	public void saveAs(ArchEVersionVO newVersion) throws ArchEException {
		
		if(responsibilityStructure != null){
			// Save responsibilities, their relations, and the translation relations
			responsibilityStructure.saveAs(newVersion);
		}
				
		if(view != null){
			// Save the view		
			view.saveAs(newVersion);					
		}
	}
	
	/**Delete this architecture from DB
	 * 
	 * @throws ArchEException
	 */
	public void delete() throws ArchEException{
		try{			
			// TODO: Need to check if this line works or not
			ArchECoreDataProvider.getSessionFactory().getCurrentSession().delete(versionVO);		
			
			// As an alternative implementation, we can consider the following code

//			// Get the current responsibility structure
//			ArchECoreResponsibilityStructure coreRS = 
//					(ArchECoreResponsibilityStructure)this.getResponsibilityStrcuture();
//	    	
//			// Delete responsibilities, their relations, and the translation relations
			// from DB
//			coreRS.delete();
//			
//			
//			// Get the current view		
//			ArchECoreView coreView = (ArchECoreView)this.getView();
//			
//			// Delete the view from DB		
//			coreView.delete();			
			
		} catch (HibernateException ex){
	        throw new ArchEException(ex.getMessage(),ex.getCause());			
		}				
	}

}
